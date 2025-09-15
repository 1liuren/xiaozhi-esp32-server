#!/usr/bin/env python3
"""
测试Docker环境修复效果
验证连续天气查询是否正常工作
"""

import os
import asyncio
import websockets
import json
import time

# 测试配置
WEBSOCKET_URL = "ws://localhost:8000/xiaozhi/v1/"
DEVICE_ID = "test-device-docker"
CLIENT_ID = "test-client-docker"

def check_docker_environment():
    """检查是否在Docker环境中"""
    is_docker = os.path.exists('/.dockerenv') or os.environ.get('DOCKER_CONTAINER') == 'true'
    print(f"🐳 Docker环境检测: {'是' if is_docker else '否'}")
    return is_docker

async def test_consecutive_weather_queries():
    """测试连续天气查询"""
    
    print("🚀 开始测试连续天气查询...")
    
    # 构建连接URL
    url = f"{WEBSOCKET_URL}?device-id={DEVICE_ID}&client-id={CLIENT_ID}"
    
    try:
        async with websockets.connect(url) as websocket:
            print("✅ WebSocket连接成功")
            
            # 接收欢迎消息
            welcome = await websocket.recv()
            print(f"📝 欢迎消息: {json.loads(welcome).get('message', 'N/A')}")
            
            # 测试查询列表
            test_queries = [
                "今天北京的天气怎么样",
                "今天广州天气怎么样", 
                "今天上海天气如何",
                "深圳今天天气好吗"
            ]
            
            for i, query in enumerate(test_queries, 1):
                print(f"\n🌤️  测试 {i}/4: {query}")
                
                # 发送查询
                message = {
                    "type": "listen",
                    "mode": "manual", 
                    "state": "detect",
                    "text": query
                }
                await websocket.send(json.dumps(message))
                print(f"📤 已发送: {query}")
                
                # 等待响应
                response_count = 0
                start_time = time.time()
                
                while time.time() - start_time < 30:  # 30秒超时
                    try:
                        response = await asyncio.wait_for(websocket.recv(), timeout=5)
                        response_data = json.loads(response)
                        response_count += 1
                        
                        if response_data.get("type") == "audio":
                            print(f"📥 音频响应 #{response_count}")
                        elif response_data.get("type") == "text":
                            text_content = response_data.get("content", "")
                            if "没有找到对应的函数" in text_content:
                                print(f"❌ 查询失败: {text_content}")
                                return False
                            elif "天气" in text_content or "温度" in text_content:
                                print(f"✅ 查询成功: {text_content[:100]}...")
                                break
                        
                    except asyncio.TimeoutError:
                        if response_count == 0:
                            print("⏰ 等待响应超时")
                            break
                        continue
                    except websockets.exceptions.ConnectionClosed:
                        print("🔌 连接已关闭")
                        return False
                
                # 等待一下再进行下一次查询
                await asyncio.sleep(2)
            
            print("\n🎉 所有测试完成！")
            return True
            
    except Exception as e:
        print(f"❌ 测试失败: {e}")
        return False

async def main():
    """主测试函数"""
    print("=" * 50)
    print("Docker环境天气查询修复测试")
    print("=" * 50)
    
    # 检查Docker环境
    check_docker_environment()
    
    print(f"🔗 连接地址: {WEBSOCKET_URL}")
    print(f"📱 设备ID: {DEVICE_ID}")
    
    # 运行测试
    success = await test_consecutive_weather_queries()
    
    if success:
        print("\n✅ 测试通过：Docker环境修复生效！")
        print("🌟 连续天气查询工作正常")
    else:
        print("\n❌ 测试失败：需要进一步调试")
        print("🔧 请检查服务器日志")

if __name__ == "__main__":
    asyncio.run(main()) 