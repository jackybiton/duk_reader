$ErrorActionPreference = 'Stop'

Add-Type -AssemblyName System.Runtime.WindowsRuntime
[void][Windows.Media.SpeechSynthesis.SpeechSynthesizer, Windows.Media.SpeechSynthesis, ContentType = WindowsRuntime]

$synth = [Windows.Media.SpeechSynthesis.SpeechSynthesizer]::new()
$hebrewVoice = [Windows.Media.SpeechSynthesis.SpeechSynthesizer]::AllVoices |
    Where-Object { $_.Language -eq 'he-IL' } |
    Select-Object -First 1

if ($null -eq $hebrewVoice) {
    [Console]::Out.WriteLine('ERROR|NO_HEBREW_VOICE')
    [Console]::Out.Flush()
    exit 2
}

$synth.Voice = $hebrewVoice
$asTaskMethod = [System.WindowsRuntimeSystemExtensions].GetMethods() |
    Where-Object { $_.Name -eq 'AsTask' -and $_.IsGenericMethod -and $_.GetParameters().Count -eq 1 } |
    Select-Object -First 1
$closedMethod = $asTaskMethod.MakeGenericMethod([Windows.Media.SpeechSynthesis.SpeechSynthesisStream])
$wavPath = Join-Path $env:TEMP ("duk-reader-voice-" + $PID + ".wav")

[Console]::Out.WriteLine('READY|' + $hebrewVoice.DisplayName)
[Console]::Out.Flush()

try {
    while (($line = [Console]::In.ReadLine()) -ne $null) {
        if ($line -eq 'QUIT') { break }
        if (-not $line.StartsWith('SPEAK|')) { continue }

        try {
            $encoded = $line.Substring(6)
            $ssml = [System.Text.Encoding]::UTF8.GetString([System.Convert]::FromBase64String($encoded))
            $operation = $synth.SynthesizeSsmlToStreamAsync($ssml)
            $task = $closedMethod.Invoke($null, @($operation))
            $task.Wait()
            $speechStream = $task.Result
            $inputStream = [System.IO.WindowsRuntimeStreamExtensions]::AsStreamForRead($speechStream)
            $fileStream = [System.IO.File]::Create($wavPath)
            $inputStream.CopyTo($fileStream)
            $fileStream.Dispose()
            $inputStream.Dispose()
            $speechStream.Dispose()

            $player = [System.Media.SoundPlayer]::new($wavPath)
            $player.PlaySync()
            $player.Dispose()
            [Console]::Out.WriteLine('DONE')
            [Console]::Out.Flush()
        }
        catch {
            $message = [System.Convert]::ToBase64String([System.Text.Encoding]::UTF8.GetBytes($_.Exception.Message))
            [Console]::Out.WriteLine('ERROR|' + $message)
            [Console]::Out.Flush()
        }
    }
}
finally {
    $synth.Dispose()
    Remove-Item -LiteralPath $wavPath -Force -ErrorAction SilentlyContinue
}
