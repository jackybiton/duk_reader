#define MyAppName "קורא דוחות ללקוחות"
#define MyAppVersion "1.0.9"
#define MyAppPublisher "Duk"
#define MyAppExeName "DukReportReaderClients.exe"

[Setup]
AppId={{EB26D42B-B7E6-4542-8D4F-316526902F23}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={localappdata}\Programs\DukReportReaderClients
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
PrivilegesRequired=lowest
OutputDir=..\..\outputs
OutputBaseFilename=DukReportReaderClients-Setup-{#MyAppVersion}
SetupIconFile=app.ico
UninstallDisplayIcon={app}\{#MyAppExeName}
Compression=lzma2/max
SolidCompression=yes
WizardStyle=modern
CloseApplications=yes
RestartApplications=no
ChangesAssociations=no
MinVersion=10.0

[Languages]
Name: "hebrew"; MessagesFile: "compiler:Languages\Hebrew.isl"

[Tasks]
Name: "desktopicon"; Description: "יצירת קיצור דרך בשולחן העבודה"; GroupDescription: "קיצורי דרך:"; Flags: unchecked

[Files]
Source: "..\..\outputs\DukReportReader-Clients-1.0.9\DukReportReaderClients.exe"; DestDir: "{app}"; Flags: ignoreversion restartreplace uninsrestartdelete

[Icons]
Name: "{group}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

[Run]
Filename: "{app}\{#MyAppExeName}"; Description: "הפעלת {#MyAppName}"; Flags: nowait postinstall skipifsilent

[Code]
function PrepareToInstall(var NeedsRestart: Boolean): String;
var
  ResultCode: Integer;
begin
  { PyInstaller keeps a small parent process alongside the visible app. }
  { First request a normal close so the app can save its current state. }
  Exec(ExpandConstant('{sys}\taskkill.exe'),
    '/T /IM "{#MyAppExeName}"', '', SW_HIDE,
    ewWaitUntilTerminated, ResultCode);
  Sleep(3000);
  { Then stop only a leftover PyInstaller parent that still holds the EXE. }
  Exec(ExpandConstant('{sys}\taskkill.exe'),
    '/F /T /IM "{#MyAppExeName}"', '', SW_HIDE,
    ewWaitUntilTerminated, ResultCode);
  Sleep(750);
  Result := '';
end;
