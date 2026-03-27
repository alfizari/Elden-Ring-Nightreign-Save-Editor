# -*- mode: python ; coding: utf-8 -*-
import os

a = Analysis(
    ['Final.py'],
    pathex=[os.getcwd()],
    datas=[
        (os.path.join(os.getcwd(), 'src', 'Resources'), 'Resources'),
    ],
)

pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name='Elden_Ring_Save_Editor',
    upx=True,
    console=False,
    windowed=True,
)

coll = COLLECT(
    exe,
    a.binaries,
    a.zipfiles,
    a.datas,
    upx=True,
    name='Elden_Ring_Save_Editor',
)

app = BUNDLE(
    coll,
    name='Elden_Ring_Save_Editor_App.app',
)
