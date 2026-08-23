@echo off
setlocal
chcp 65001 >nul
cd /d "%~dp0"
py -3.11 -m pip install -r requirements.txt
if errorlevel 1 (
  echo.
  echo [失败] 请确认已安装 64 位 Python 3.11，并可通过 py -3.11 调用。
  pause
  exit /b 1
)
echo.
echo [完成] Python 依赖已安装。
pause
