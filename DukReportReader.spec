# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path

from PyInstaller.utils.hooks import collect_data_files, collect_dynamic_libs


ROOT = Path.cwd()


def add_if_exists(items, source: str, destination: str) -> None:
    path = ROOT / source
    if path.exists():
        items.append((str(path), destination))


datas = []
add_if_exists(datas, "tts_worker.ps1", ".")
add_if_exists(datas, "app.ico", ".")
add_if_exists(datas, "torah_nikud.json", ".")
add_if_exists(datas, "offline_voice_models", "offline_voice_models")
add_if_exists(datas, "private_voice_models", "private_voice_models")
add_if_exists(datas, "tessdata", "tessdata")

datas += collect_data_files("language_tags")
datas += collect_data_files("espeakng_loader")
binaries = collect_dynamic_libs("espeakng_loader")


a = Analysis(
    [str(ROOT / "duk_reader.py")],
    pathex=[str(ROOT)],
    binaries=binaries,
    datas=datas,
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

icon = [str(ROOT / "app.ico")] if (ROOT / "app.ico").is_file() else None

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name="DukReportReader",
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=icon,
)
