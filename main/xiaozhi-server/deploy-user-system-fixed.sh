#!/bin/bash

# 设置颜色
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

printf "${BLUE}======================================${NC}\n"
printf "${BLUE}   小智ESP32服务器 - 完整用户系统部署${NC}\n"
printf "${BLUE}======================================${NC}\n"
printf "\n"

# 检查Docker是否运行
if ! docker ps >/dev/null 2>&1; then
    printf "${RED}❌ Docker未运行或无权限访问！${NC}\n"
    exit 1
fi

# 检查容器是否存在
if ! docker ps -a --format "table {{.Names}}" | grep -q "xiaozhi-esp32-server"; then
    printf "${RED}❌ 容器 xiaozhi-esp32-server 不存在！${NC}\n"
    exit 1
fi

# 创建必要的目录结构
printf "${YELLOW}正在创建目录结构...${NC}\n"
docker exec xiaozhi-esp32-server mkdir -p /opt/xiaozhi-esp32-server/core/interceptors >/dev/null 2>&1
docker exec xiaozhi-esp32-server mkdir -p /opt/xiaozhi-esp32-server/core/api >/dev/null 2>&1
docker exec xiaozhi-esp32-server mkdir -p /opt/xiaozhi-esp32-server/core/database >/dev/null 2>&1
printf "${GREEN}✅ 目录结构创建完成${NC}\n"

# 部署文件函数
deploy_file() {
    local file_path=$1
    local container_path=$2
    local description=$3
    local step=$4
    local total=$5
    
    printf "${YELLOW}[$step/$total] 正在部署$description...${NC}\n"
    
    if docker cp "$file_path" "xiaozhi-esp32-server:$container_path"; then
        printf "${GREEN}✅ $description部署完成${NC}\n"
        return 0
    else
        printf "${RED}❌ $description部署失败！${NC}\n"
        return 1
    fi
}

# 部署所有文件
deploy_file "core/interceptors/message_interceptor.py" "/opt/xiaozhi-esp32-server/core/interceptors/message_interceptor.py" "消息拦截器" 1 8 || exit 1

deploy_file "core/interceptors/custom_handlers.py" "/opt/xiaozhi-esp32-server/core/interceptors/custom_handlers.py" "自定义处理器" 2 8 || exit 1

deploy_file "core/api/interceptor_handler.py" "/opt/xiaozhi-esp32-server/core/api/interceptor_handler.py" "拦截器API处理器" 3 8 || exit 1

deploy_file "core/database/user_manager.py" "/opt/xiaozhi-esp32-server/core/database/user_manager.py" "用户数据库管理器" 4 8 || exit 1

deploy_file "core/api/user_handler.py" "/opt/xiaozhi-esp32-server/core/api/user_handler.py" "用户API处理器" 5 8 || exit 1

deploy_file "core/connection.py" "/opt/xiaozhi-esp32-server/core/connection.py" "WebSocket连接处理器" 6 8 || exit 1

deploy_file "core/http_server.py" "/opt/xiaozhi-esp32-server/core/http_server.py" "HTTP服务器" 7 8 || exit 1

# 重启容器
printf "${YELLOW}[8/8] 正在重启Docker容器...${NC}\n"
if docker restart xiaozhi-esp32-server; then
    printf "${GREEN}✅ Docker容器重启完成${NC}\n"
else
    printf "${RED}❌ Docker容器重启失败！${NC}\n"
    exit 1
fi

printf "\n"
printf "${BLUE}======================================${NC}\n"
printf "${BLUE}             部署完成！${NC}\n"
printf "${BLUE}======================================${NC}\n"
printf "\n"
printf "${GREEN}📊 拦截器状态API:    ${NC}http://localhost:8089/interceptor/status\n"
printf "${GREEN}👥 用户列表API:      ${NC}http://localhost:8089/users\n"
printf "${GREEN}📈 用户统计API:      ${NC}http://localhost:8089/users/stats\n"
printf "${GREEN}💰 用户充值API:      ${NC}POST http://localhost:8089/users/{用户ID}/recharge\n"
printf "${GREEN}🔋 用户电量API:      ${NC}POST http://localhost:8089/users/{用户ID}/battery\n"
printf "\n"

printf "${YELLOW}正在等待服务启动（30秒）...${NC}\n"
sleep 30

printf "${YELLOW}正在测试API连接...${NC}\n"
if curl -s http://localhost:8089/interceptor/status >/dev/null 2>&1; then
    printf "${GREEN}✅ API服务正常运行！${NC}\n"
else
    printf "${YELLOW}⚠️  API服务可能还在启动中，请稍等片刻后手动测试${NC}\n"
fi

printf "\n"
printf "${GREEN}🎉 完整用户系统部署成功！${NC}\n"

# 显示测试命令
printf "\n"
printf "${BLUE}快速测试命令：${NC}\n"
printf "${GREEN}# 查看拦截器状态${NC}\n"
printf "curl http://localhost:8089/interceptor/status\n"
printf "\n"
printf "${GREEN}# 查看所有用户${NC}\n"
printf "curl http://localhost:8089/users\n"
printf "\n"
printf "${GREEN}# 给用户充值100元（替换用户ID）${NC}\n"
printf 'curl -X POST http://localhost:8089/users/19:13:6A:AC:06:2D/recharge -H "Content-Type: application/json" -d '\''{"amount": 100}'\''\n'
printf "\n" 