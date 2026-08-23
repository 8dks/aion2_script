@echo off
setlocal
chcp 65001 >nul
set "PYTHONUTF8=1"
set "PYTHONDONTWRITEBYTECODE=1"
set "TESSDATA_PREFIX=%~dp0tessdata\tessdata-main"
cd /d "%~dp0"
py -3.11 DD.py
if errorlevel 1 pause
