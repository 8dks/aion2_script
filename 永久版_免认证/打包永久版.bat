@echo off
setlocal
chcp 65001 >nul
cd /d "%~dp0"
py -3.11 -m pip install -r requirements.txt
if errorlevel 1 goto :failed
py -3.11 -m pip install "pyinstaller>=6.10"
if errorlevel 1 goto :failed
py -3.11 -m PyInstaller --noconfirm --clean K3M2_永久版.spec
if errorlevel 1 goto :failed
echo.
echo [完成] 永久版已生成：dist\K3M2_永久版.exe
pause
exit /b 0

:failed
echo.
echo [失败] 打包未完成，请检查上方错误信息。
pause
exit /b 1
