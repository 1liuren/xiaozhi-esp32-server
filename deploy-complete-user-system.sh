#!/bin/bash

# 设置颜色
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}======================================${NC}"
echo -e "${BLUE}   小智ESP32服务器 - 完整用户系统部署${NC}"
echo -e "${BLUE}======================================${NC}"
echo

# 检查Docker是否运行
if ! docker ps >/dev/null 2>&1; then
    echo -e "${RED}❌ Docker未运行或无权限访问！${NC}"
    exit 1
fi

# 检查容器是否存在
if ! docker ps -a --format "table {{.Names}}" | grep -q "xiaozhi-esp32-server"; then
    echo -e "${RED}❌ 容器 xiaozhi-esp32-server 不存在！${NC}"
    exit 1
fi

# 部署文件函数
deploy_file() {
    local file_path=$1
    local container_path=$2
    local description=$3
    local step=$4
    local total=$5
    
    echo -e "${YELLOW}[$step/$total] 正在部署$description...${NC}"
    
    if docker cp "$file_path" "xiaozhi-esp32-server:$container_path"; then
        echo -e "${GREEN}✅ $description部署完成${NC}"
        return 0
    else
        echo -e "${RED}❌ $description部署失败！${NC}"
        return 1
    fi
}

# 部署所有文件
deploy_file "main/xiaozhi-server/core/interceptors/message_interceptor.py" "/app/core/interceptors/message_interceptor.py" "消息拦截器" 1 8 || exit 1

deploy_file "main/xiaozhi-server/core/interceptors/custom_handlers.py" "/app/core/interceptors/custom_handlers.py" "自定义处理器" 2 8 || exit 1

deploy_file "main/xiaozhi-server/core/api/interceptor_handler.py" "/app/core/api/interceptor_handler.py" "拦截器API处理器" 3 8 || exit 1

deploy_file "main/xiaozhi-server/core/database/user_manager.py" "/app/core/database/user_manager.py" "用户数据库管理器" 4 8 || exit 1

deploy_file "main/xiaozhi-server/core/api/user_handler.py" "/app/core/api/user_handler.py" "用户API处理器" 5 8 || exit 1

deploy_file "main/xiaozhi-server/core/connection.py" "/app/core/connection.py" "WebSocket连接处理器" 6 8 || exit 1

deploy_file "main/xiaozhi-server/core/http_server.py" "/app/core/http_server.py" "HTTP服务器" 7 8 || exit 1

# 重启容器
echo -e "${YELLOW}[8/8] 正在重启Docker容器...${NC}"
if docker restart xiaozhi-esp32-server; then
    echo -e "${GREEN}✅ Docker容器重启完成${NC}"
else
    echo -e "${RED}❌ Docker容器重启失败！${NC}"
    exit 1
fi

echo
echo -e "${BLUE}======================================${NC}"
echo -e "${BLUE}             部署完成！${NC}"
echo -e "${BLUE}======================================${NC}"
echo
echo -e "${GREEN}📊 拦截器状态API:    ${NC}http://localhost:8089/interceptor/status"
echo -e "${GREEN}👥 用户列表API:      ${NC}http://localhost:8089/users"
echo -e "${GREEN}📈 用户统计API:      ${NC}http://localhost:8089/users/stats"
echo -e "${GREEN}💰 用户充值API:      ${NC}POST http://localhost:8089/users/{用户ID}/recharge"
echo -e "${GREEN}🔋 用户电量API:      ${NC}POST http://localhost:8089/users/{用户ID}/battery"
echo

echo -e "${YELLOW}正在等待服务启动（30秒）...${NC}"
sleep 30

echo -e "${YELLOW}正在测试API连接...${NC}"
if curl -s http://localhost:8089/interceptor/status >/dev/null 2>&1; then
    echo -e "${GREEN}✅ API服务正常运行！${NC}"
else
    echo -e "${YELLOW}⚠️  API服务可能还在启动中，请稍等片刻后手动测试${NC}"
fi

echo
echo -e "${GREEN}🎉 完整用户系统部署成功！${NC}"

# 显示测试命令
echo
echo -e "${BLUE}快速测试命令：${NC}"
echo -e "${GREEN}# 查看拦截器状态${NC}"
echo "curl http://localhost:8089/interceptor/status"
echo
echo -e "${GREEN}# 查看所有用户${NC}"
echo "curl http://localhost:8089/users"
echo
echo -e "${GREEN}# 给用户充值100元（替换用户ID）${NC}"
echo 'curl -X POST http://localhost:8089/users/19:13:6A:AC:06:2D/recharge -H "Content-Type: application/json" -d '"'"'{"amount": 100}'"'" 