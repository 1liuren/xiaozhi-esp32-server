#!/usr/bin/env python3
"""
测试工具调用机制
显示详细的调用流程和调试信息
"""

import asyncio
import websockets
import json
import time

# 测试配置
WEBSOCKET_URL = "ws://localhost:8000/xiaozhi/v1/"
DEVICE_ID = "debug-device"
CLIENT_ID = "debug-client"

async def test_tool_calling_flow():
    """测试工具调用流程"""
    
    print("🔧 开始测试工具调用流程...")
    print("=" * 60)
    
    # 构建连接URL
    url = f"{WEBSOCKET_URL}?device-id={DEVICE_ID}&client-id={CLIENT_ID}"
    
    try:
        async with websockets.connect(url) as websocket:
            print("✅ WebSocket连接成功")
            
            # 接收欢迎消息
            welcome = await websocket.recv()
            welcome_data = json.loads(welcome)
            print(f"📝 欢迎消息收到，session_id: {welcome_data.get('session_id', 'N/A')}")
            
            # 测试天气查询
            test_queries = [
                "今天广州天气怎么样",  # 应该触发工具调用
                "你好吗",              # 不应该触发工具调用
                "北京天气如何",        # 应该触发工具调用
            ]
            
            for i, query in enumerate(test_queries, 1):
                print(f"\n🧪 测试 {i}: {query}")
                print("-" * 40)
                
                # 发送查询
                message = {
                    "type": "listen",
                    "mode": "manual", 
                    "state": "detect",
                    "text": query
                }
                await websocket.send(json.dumps(message))
                print(f"📤 已发送: {query}")
                
                # 收集响应
                start_time = time.time()
                response_count = 0
                got_text_response = False
                
                while time.time() - start_time < 20:  # 20秒超时
                    try:
                        response = await asyncio.wait_for(websocket.recv(), timeout=3)
                        response_data = json.loads(response)
                        response_count += 1
                        
                        msg_type = response_data.get("type", "unknown")
                        
                        if msg_type == "audio":
                            print(f"📥 音频响应 #{response_count}")
                        elif msg_type == "text":
                            content = response_data.get("content", "")
                            print(f"📥 文本响应: {content}")
                            got_text_response = True
                            
                            # 分析响应内容
                            if "没有找到对应的函数" in content:
                                print("❌ 工具调用失败：没有找到对应的函数")
                            elif any(word in content for word in ["天气", "温度", "阴", "晴", "雨", "雪"]):
                                print("✅ 工具调用成功：返回了天气信息")
                            elif query in ["你好吗"] and "天气" not in content:
                                print("✅ 正确处理：普通对话没有调用工具")
                            
                            break
                        
                    except asyncio.TimeoutError:
                        if response_count == 0:
                            print("⏰ 等待响应超时")
                            break
                        continue
                    except websockets.exceptions.ConnectionClosed:
                        print("🔌 连接已关闭")
                        return
                    except json.JSONDecodeError:
                        print("⚠️  收到非JSON响应")
                        continue
                
                if not got_text_response:
                    print("❌ 未收到有效的文本响应")
                
                # 等待一下再进行下一次测试
                await asyncio.sleep(2)
            
            print("\n🎉 测试完成！")
            print("=" * 60)
            print("📋 期望看到的日志模式:")
            print("   🛠️  获取到 X 个可用函数")
            print("   🤖 正在调用支持函数的LLM接口")
            print("   🔧 检测到工具调用")
            print("   📝 函数名: get_weather")
            print("   🚀 准备执行函数调用")
            print("   ✅ func_handler 可用，开始执行...")
            print("   🎯 函数执行结果: REQLLM")
            
    except Exception as e:
        print(f"❌ 测试失败: {e}")

if __name__ == "__main__":
    print("🔍 工具调用机制测试")
    print("此脚本将测试天气查询功能，并观察工具调用流程")
    print("请确保服务器已启动并监控日志输出")
    print()
    
    asyncio.run(test_tool_calling_flow()) 