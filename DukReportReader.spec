# -*- mode: python ; coding: utf-8 -*-

from PyInstaller.utils.hooks import collect_data_files, collect_dynamic_libs


a = Analysis(
    ['C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/duk_reader.py'],
    pathex=['C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/runtime_deps'],
    binaries=collect_dynamic_libs('espeakng_loader'),
    datas=[('C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/tts_worker.ps1', '.'), ('C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/app.ico', '.'), ('C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/torah_nikud.json', '.'), ('C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/offline_voice_models', 'offline_voice_models'), ('C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/private_voice_models', 'private_voice_models'), ('C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/tessdata', 'tessdata')] + collect_data_files('language_tags') + collect_data_files('espeakng_loader'),
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='DukReportReader',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=['C:/Users/yaakov/Documents/Codex/2026-08-11/new-chat/work/duk_reader/app.ico'],
)
