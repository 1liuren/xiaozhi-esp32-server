#!/usr/bin/env python3
"""
天气功能调试脚本
用于排查"没有找到对应的函数"问题
"""

import sys
import os
import json

# 添加项目路径
sys.path.insert(0, '/root/xiaozhi-esp32-server/main/xiaozhi-server')

def test_weather_function():
    """测试天气功能是否正常"""
    
    print("🔍 开始检查天气功能状态...")
    
    try:
        # 1. 检查插件注册情况
        print("\n1️⃣ 检查插件注册...")
        from plugins_func.loadplugins import auto_import_modules
        auto_import_modules("plugins_func.functions")
        
        from plugins_func.register import all_function_registry
        
        print(f"✅ 已注册的函数: {list(all_function_registry.keys())}")
        
        if 'get_weather' in all_function_registry:
            print("✅ get_weather 函数已注册")
        else:
            print("❌ get_weather 函数未注册!")
            return False
            
    except Exception as e:
        print(f"❌ 插件加载失败: {e}")
        return False
    
    try:
        # 2. 检查配置文件
        print("\n2️⃣ 检查配置文件...")
        from config.config_loader import get_config
        config = get_config()
        
        # 检查意图识别配置
        intent_type = config.get('selected_module', {}).get('Intent', '')
        print(f"意图识别类型: {intent_type}")
        
        if intent_type == 'function_call':
            functions = config.get('Intent', {}).get('function_call', {}).get('functions', [])
            print(f"配置的函数列表: {functions}")
            
            if 'get_weather' in functions:
                print("✅ get_weather 在配置中已启用")
            else:
                print("❌ get_weather 在配置中未启用!")
                return False
        else:
            print(f"❌ 意图识别类型错误，当前为: {intent_type}, 应该为: function_call")
            return False
            
        # 检查天气插件配置
        weather_config = config.get('plugins', {}).get('get_weather', {})
        if weather_config:
            print(f"✅ 天气插件配置存在: {weather_config}")
        else:
            print("❌ 天气插件配置缺失!")
            return False
            
    except Exception as e:
        print(f"❌ 配置检查失败: {e}")
        return False
    
    try:
        # 3. 测试函数调用
        print("\n3️⃣ 测试函数调用...")
        
        # 模拟连接对象
        class MockConnection:
            def __init__(self):
                self.config = config
                self.client_ip = '127.0.0.1'
        
        conn = MockConnection()
        
        # 获取天气函数
        weather_func = all_function_registry['get_weather']
        print(f"✅ 天气函数对象: {weather_func}")
        
        # 测试调用
        print("🧪 测试调用天气函数...")
        result = weather_func.func(conn, location="广州", lang="zh_CN")
        
        if result and hasattr(result, 'action'):
            print(f"✅ 函数调用成功，返回类型: {result.action}")
            if hasattr(result, 'result') and result.result:
                print(f"📊 返回内容前100字符: {str(result.result)[:100]}...")
            return True
        else:
            print(f"❌ 函数调用失败，返回: {result}")
            return False
            
    except Exception as e:
        print(f"❌ 函数调用测试失败: {e}")
        return False

def generate_fix_suggestions():
    """生成修复建议"""
    
    print("\n🛠️ 修复建议:")
    print("=" * 50)
    
    print("\n📋 1. 检查配置文件 (config.yaml):")
    print("   确保以下配置正确:")
    print("   selected_module:")
    print("     Intent: function_call")
    print()
    print("   Intent:")
    print("     function_call:")
    print("       functions:")
    print("         - get_weather")
    
    print("\n📋 2. 重启服务:")
    print("   修改配置后，需要重启小智服务")
    
    print("\n📋 3. 检查LLM支持:")
    print("   确保使用的LLM支持function_call功能")
    print("   推荐使用: ChatGLMLLM (glm-4-flash) 或 DoubaoLLM")
    
    print("\n📋 4. 测试命令:")
    print("   重启后，尝试说:")
    print("   - 今天天气怎么样？")
    print("   - 广州天气")
    print("   - 北京的天气预报")

if __name__ == "__main__":
    print("🌤️ 小智天气功能调试工具")
    print("=" * 50)
    
    success = test_weather_function()
    
    if success:
        print("\n🎉 天气功能检查通过!")
        print("如果仍然遇到问题，可能是LLM没有正确识别意图。")
        print("请尝试更明确的表达，如：'查询广州天气' 或 '今天天气如何'")
    else:
        print("\n❌ 天气功能存在问题!")
        generate_fix_suggestions()
    
    print("\n" + "=" * 50) 