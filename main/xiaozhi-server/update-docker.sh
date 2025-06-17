#!/bin/bash
# Docker代码同步更新脚本

echo "🔄 开始同步代码到Docker容器..."

# 检查容器是否运行
if [ ! "$(docker ps -q -f name=xiaozhi-esp32-server)" ]; then
    echo "❌ 容器 xiaozhi-esp32-server 未运行，请先启动容器"
    exit 1
fi

# 复制修改的文件到容器
echo "📁 复制拦截器代码..."
docker cp core/interceptors xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/ 2>/dev/null
docker cp core/api/interceptor_handler.py xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/api/ 2>/dev/null
docker cp core/connection.py xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/ 2>/dev/null
docker cp core/http_server.py xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/core/ 2>/dev/null

# 复制配置文件（如果需要）
if [ -f "data/.config.yaml" ]; then
    echo "⚙️ 同步配置文件..."
    docker cp data/.config.yaml xiaozhi-esp32-server:/opt/xiaozhi-esp32-server/data/ 2>/dev/null
fi

echo "🔄 重启容器以应用更改..."
docker-compose restart xiaozhi-esp32-server

echo "✅ 代码同步完成！"
echo "📊 检查拦截器状态："
sleep 5
curl -s http://localhost:8003/interceptor/status | jq '.interceptor_stats' || echo "等待服务启动..."

echo ""
echo "🎯 监控日志："
echo "docker logs -f xiaozhi-esp32-server | grep '截获请求\\|用户说话\\|消息拦截器'" 