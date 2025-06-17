@echo off
REM 用户管理系统部署脚本 (Windows版本)

echo 🚀 开始部署用户管理系统...

REM 检查容器是否运行
docker ps -q -f name=xiaozhi-esp32-server >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ 容器 xiaozhi-esp32-server 未运行，请先启动容器
    pause
    exit /b 1
)

echo 📁 复制用户管理系统代码...

REM 复制数据库管理模块
docker cp core\database xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/ >nul 2>&1

REM 复制用户API处理器
docker cp core\api\user_handler.py xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/api/ >nul 2>&1

REM 复制更新的拦截器代码
docker cp core\interceptors xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/ >nul 2>&1

REM 复制更新的HTTP服务器
docker cp core\http_server.py xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/ >nul 2>&1

echo 🔄 重启容器以应用更改...
docker-compose restart xiaozhi-esp32-server

echo ✅ 用户管理系统部署完成！

echo.
echo 📊 等待服务启动...
timeout /t 10 /nobreak >nul

echo.
echo 🎯 测试用户管理接口：

echo 📋 获取所有用户：
curl -s http://localhost:8089/users

echo.
echo 📊 获取用户统计：
curl -s http://localhost:8089/users/stats

echo.
echo 💡 API接口说明：
echo - GET  /users          - 获取所有用户
echo - GET  /users/stats    - 获取统计信息
echo - GET  /users/{id}     - 获取指定用户信息
echo - POST /users          - 创建用户
echo - POST /users/{id}/recharge - 用户充值
echo - POST /users/{id}/battery  - 更新电量

echo.
echo 🎉 部署完成！用户每次请求将自动扣除0.5余额

pause 