@echo off
chcp 65001 >nul
echo ======================================
echo    小智ESP32服务器 - 完整用户系统部署
echo ======================================
echo.

echo [1/8] 正在部署消息拦截器...
docker cp main/xiaozhi-server/core/interceptors/message_interceptor.py xiaozhi-esp32-server:/app/core/interceptors/message_interceptor.py
if %errorlevel% neq 0 (
    echo ❌ 消息拦截器部署失败！
    pause
    exit /b 1
)
echo ✅ 消息拦截器部署完成

echo [2/8] 正在部署自定义处理器...
docker cp main/xiaozhi-server/core/interceptors/custom_handlers.py xiaozhi-esp32-server:/app/core/interceptors/custom_handlers.py
if %errorlevel% neq 0 (
    echo ❌ 自定义处理器部署失败！
    pause
    exit /b 1
)
echo ✅ 自定义处理器部署完成

echo [3/8] 正在部署拦截器API处理器...
docker cp main/xiaozhi-server/core/api/interceptor_handler.py xiaozhi-esp32-server:/app/core/api/interceptor_handler.py
if %errorlevel% neq 0 (
    echo ❌ 拦截器API处理器部署失败！
    pause
    exit /b 1
)
echo ✅ 拦截器API处理器部署完成

echo [4/8] 正在部署用户数据库管理器...
docker cp main/xiaozhi-server/core/database/user_manager.py xiaozhi-esp32-server:/app/core/database/user_manager.py
if %errorlevel% neq 0 (
    echo ❌ 用户数据库管理器部署失败！
    pause
    exit /b 1
)
echo ✅ 用户数据库管理器部署完成

echo [5/8] 正在部署用户API处理器...
docker cp main/xiaozhi-server/core/api/user_handler.py xiaozhi-esp32-server:/app/core/api/user_handler.py
if %errorlevel% neq 0 (
    echo ❌ 用户API处理器部署失败！
    pause
    exit /b 1
)
echo ✅ 用户API处理器部署完成

echo [6/8] 正在部署WebSocket连接处理器...
docker cp main/xiaozhi-server/core/connection.py xiaozhi-esp32-server:/app/core/connection.py
if %errorlevel% neq 0 (
    echo ❌ WebSocket连接处理器部署失败！
    pause
    exit /b 1
)
echo ✅ WebSocket连接处理器部署完成

echo [7/8] 正在部署HTTP服务器...
docker cp main/xiaozhi-server/core/http_server.py xiaozhi-esp32-server:/app/core/http_server.py
if %errorlevel% neq 0 (
    echo ❌ HTTP服务器部署失败！
    pause
    exit /b 1
)
echo ✅ HTTP服务器部署完成

echo [8/8] 正在重启Docker容器...
docker restart xiaozhi-esp32-server
if %errorlevel% neq 0 (
    echo ❌ Docker容器重启失败！
    pause
    exit /b 1
)
echo ✅ Docker容器重启完成

echo.
echo ======================================
echo             部署完成！
echo ======================================
echo.
echo 📊 拦截器状态API:    http://localhost:8089/interceptor/status
echo 👥 用户列表API:      http://localhost:8089/users
echo 📈 用户统计API:      http://localhost:8089/users/stats
echo 💰 用户充值API:      POST http://localhost:8089/users/{用户ID}/recharge
echo 🔋 用户电量API:      POST http://localhost:8089/users/{用户ID}/battery
echo.
echo 正在等待服务启动（30秒）...
timeout /t 30 /nobreak >nul

echo 正在测试API连接...
curl -s http://localhost:8089/interceptor/status >nul
if %errorlevel% equ 0 (
    echo ✅ API服务正常运行！
) else (
    echo ⚠️  API服务可能还在启动中，请稍等片刻后手动测试
)

echo.
echo 🎉 完整用户系统部署成功！
echo.
pause 