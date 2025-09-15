#!/usr/bin/env python3
"""
小智自定义天气新闻MCP服务器示例
可以通过MCP接入点方式集成到小智系统中
"""

import asyncio
import json
import sys
from typing import Any, Sequence
import httpx
from datetime import datetime

# MCP服务器框架
from mcp.server import Server
from mcp.server.models import InitializationOptions
from mcp.server.stdio import stdio_server
from mcp.types import (
    CallToolRequest,
    CallToolResult,
    ListToolsRequest,
    Tool,
    TextContent,
)

app = Server("weather-news-mcp")

# 配置API密钥
WEATHER_API_KEY = "a861d0d5e7bf4ee1a83d9a9e4f96d4da"  # 和风天气API密钥
NEWS_API_KEY = "your_news_api_key"  # 新闻API密钥（根据需要配置）


@app.list_tools()
async def list_tools() -> list[Tool]:
    """列出所有可用的工具"""
    return [
        Tool(
            name="get_realtime_weather",
            description="获取指定城市的实时天气信息，包括温度、湿度、风速等详细数据",
            inputSchema={
                "type": "object",
                "properties": {
                    "city": {
                        "type": "string",
                        "description": "城市名称，如：北京、上海、广州"
                    },
                    "language": {
                        "type": "string", 
                        "description": "返回语言，默认zh（中文）",
                        "default": "zh"
                    }
                },
                "required": ["city"]
            }
        ),
        Tool(
            name="get_weather_forecast",
            description="获取指定城市未来7天的天气预报，包括最高最低温度和天气状况",
            inputSchema={
                "type": "object",
                "properties": {
                    "city": {
                        "type": "string",
                        "description": "城市名称，如：北京、上海、广州"
                    },
                    "days": {
                        "type": "integer",
                        "description": "预报天数，1-7天，默认7天",
                        "default": 7,
                        "minimum": 1,
                        "maximum": 7
                    }
                },
                "required": ["city"]
            }
        ),
        Tool(
            name="get_hot_news",
            description="获取当前热门新闻，可以指定新闻类型和数量",
            inputSchema={
                "type": "object",
                "properties": {
                    "category": {
                        "type": "string",
                        "description": "新闻类别：general(综合)、technology(科技)、business(财经)、entertainment(娱乐)、sports(体育)",
                        "default": "general"
                    },
                    "count": {
                        "type": "integer",
                        "description": "返回新闻数量，默认5条",
                        "default": 5,
                        "minimum": 1,
                        "maximum": 20
                    },
                    "country": {
                        "type": "string",
                        "description": "国家代码，如cn(中国)、us(美国)，默认cn",
                        "default": "cn"
                    }
                },
                "required": []
            }
        ),
        Tool(
            name="search_news",
            description="根据关键词搜索相关新闻",
            inputSchema={
                "type": "object",
                "properties": {
                    "query": {
                        "type": "string",
                        "description": "搜索关键词，如：人工智能、新能源汽车等"
                    },
                    "count": {
                        "type": "integer",
                        "description": "返回新闻数量，默认5条",
                        "default": 5,
                        "minimum": 1,
                        "maximum": 20
                    },
                    "language": {
                        "type": "string",
                        "description": "新闻语言，默认zh（中文）",
                        "default": "zh"
                    }
                },
                "required": ["query"]
            }
        )
    ]


@app.call_tool()
async def call_tool(name: str, arguments: dict) -> list[TextContent]:
    """处理工具调用"""
    
    if name == "get_realtime_weather":
        return await get_realtime_weather(arguments)
    elif name == "get_weather_forecast":
        return await get_weather_forecast(arguments)
    elif name == "get_hot_news":
        return await get_hot_news(arguments)
    elif name == "search_news":
        return await search_news(arguments)
    else:
        raise ValueError(f"未知工具: {name}")


async def get_realtime_weather(args: dict) -> list[TextContent]:
    """获取实时天气"""
    city = args.get("city", "")
    language = args.get("language", "zh")
    
    try:
        # 1. 先获取城市信息
        async with httpx.AsyncClient() as client:
            geo_url = f"https://geoapi.qweather.com/v2/city/lookup"
            geo_params = {
                "location": city,
                "key": WEATHER_API_KEY,
                "lang": language
            }
            geo_response = await client.get(geo_url, params=geo_params)
            geo_data = geo_response.json()
            
            if geo_data["code"] != "200" or not geo_data.get("location"):
                return [TextContent(type="text", text=f"未找到城市：{city}")]
            
            location_id = geo_data["location"][0]["id"]
            city_name = geo_data["location"][0]["name"]
            
            # 2. 获取实时天气
            weather_url = f"https://devapi.qweather.com/v7/weather/now"
            weather_params = {
                "location": location_id,
                "key": WEATHER_API_KEY,
                "lang": language
            }
            weather_response = await client.get(weather_url, params=weather_params)
            weather_data = weather_response.json()
            
            if weather_data["code"] != "200":
                return [TextContent(type="text", text=f"获取{city}天气信息失败")]
            
            now = weather_data["now"]
            update_time = weather_data["updateTime"]
            
            result = f"""🌤️ {city_name}实时天气情况

📅 更新时间：{update_time}
🌡️ 温度：{now['temp']}°C
😌 体感温度：{now['feelsLike']}°C
☁️ 天气：{now['text']}
💨 风向：{now['windDir']} {now['windScale']}级
🌪️ 风速：{now['windSpeed']} km/h
💧 相对湿度：{now['humidity']}%
👁️ 能见度：{now['vis']} km
🌡️ 气压：{now['pressure']} hPa"""

            return [TextContent(type="text", text=result)]
            
    except Exception as e:
        return [TextContent(type="text", text=f"获取天气信息时出错：{str(e)}")]


async def get_weather_forecast(args: dict) -> list[TextContent]:
    """获取天气预报"""
    city = args.get("city", "")
    days = args.get("days", 7)
    
    try:
        async with httpx.AsyncClient() as client:
            # 1. 获取城市信息
            geo_url = f"https://geoapi.qweather.com/v2/city/lookup"
            geo_params = {
                "location": city,
                "key": WEATHER_API_KEY
            }
            geo_response = await client.get(geo_url, params=geo_params)
            geo_data = geo_response.json()
            
            if geo_data["code"] != "200" or not geo_data.get("location"):
                return [TextContent(type="text", text=f"未找到城市：{city}")]
            
            location_id = geo_data["location"][0]["id"]
            city_name = geo_data["location"][0]["name"]
            
            # 2. 获取天气预报
            forecast_url = f"https://devapi.qweather.com/v7/weather/7d"
            forecast_params = {
                "location": location_id,
                "key": WEATHER_API_KEY
            }
            forecast_response = await client.get(forecast_url, params=forecast_params)
            forecast_data = forecast_response.json()
            
            if forecast_data["code"] != "200":
                return [TextContent(type="text", text=f"获取{city}天气预报失败")]
            
            daily_forecast = forecast_data["daily"][:days]
            
            result = f"📅 {city_name}未来{days}天天气预报\n\n"
            
            for i, day in enumerate(daily_forecast):
                date = day["fxDate"]
                weekday = ["周一", "周二", "周三", "周四", "周五", "周六", "周日"][datetime.strptime(date, "%Y-%m-%d").weekday()]
                
                if i == 0:
                    day_label = "今天"
                elif i == 1:
                    day_label = "明天"
                else:
                    day_label = f"{date} {weekday}"
                
                result += f"📅 {day_label}\n"
                result += f"🌤️ {day['textDay']} 转 {day['textNight']}\n"
                result += f"🌡️ {day['tempMin']}°C ~ {day['tempMax']}°C\n"
                result += f"💨 {day['windDirDay']} {day['windScaleDay']}级\n\n"
            
            return [TextContent(type="text", text=result)]
            
    except Exception as e:
        return [TextContent(type="text", text=f"获取天气预报时出错：{str(e)}")]


async def get_hot_news(args: dict) -> list[TextContent]:
    """获取热门新闻（示例使用免费新闻API）"""
    category = args.get("category", "general")
    count = args.get("count", 5)
    country = args.get("country", "cn")
    
    # 这里使用一个免费的新闻API示例
    # 实际使用时可以替换为你偏好的新闻API
    try:
        async with httpx.AsyncClient() as client:
            # 示例：使用NewsAPI（需要API key）
            # url = f"https://newsapi.org/v2/top-headlines"
            # params = {
            #     "country": country,
            #     "category": category,
            #     "pageSize": count,
            #     "apiKey": NEWS_API_KEY
            # }
            
            # 这里使用一个模拟的新闻数据作为示例
            mock_news = [
                {
                    "title": "人工智能技术取得重大突破",
                    "description": "最新的AI研究在多个领域展现出巨大潜力...",
                    "url": "https://example.com/news1",
                    "publishedAt": "2024-01-15T10:30:00Z",
                    "source": {"name": "科技日报"}
                },
                {
                    "title": "新能源汽车市场持续火热",
                    "description": "电动汽车销量创历史新高，充电设施不断完善...",
                    "url": "https://example.com/news2", 
                    "publishedAt": "2024-01-15T09:15:00Z",
                    "source": {"name": "财经新闻"}
                },
                {
                    "title": "太空探索迎来新里程碑",
                    "description": "最新火箭发射任务圆满成功，为未来探索奠定基础...",
                    "url": "https://example.com/news3",
                    "publishedAt": "2024-01-15T08:45:00Z",
                    "source": {"name": "航天报"}
                }
            ]
            
            result = f"📰 热门新闻（{category}类别）\n\n"
            
            for i, article in enumerate(mock_news[:count], 1):
                pub_time = article["publishedAt"][:10]  # 提取日期
                result += f"{i}. 📰 {article['title']}\n"
                result += f"📅 {pub_time} | 📍 {article['source']['name']}\n"
                result += f"📝 {article['description']}\n"
                result += f"🔗 {article['url']}\n\n"
            
            result += "💡 说明：这是示例新闻数据，实际使用时需要配置真实的新闻API"
            
            return [TextContent(type="text", text=result)]
            
    except Exception as e:
        return [TextContent(type="text", text=f"获取新闻时出错：{str(e)}")]


async def search_news(args: dict) -> list[TextContent]:
    """搜索新闻"""
    query = args.get("query", "")
    count = args.get("count", 5)
    language = args.get("language", "zh")
    
    if not query:
        return [TextContent(type="text", text="请提供搜索关键词")]
    
    try:
        # 模拟搜索结果
        mock_results = [
            {
                "title": f"关于'{query}'的最新报道",
                "description": f"详细报道了{query}相关的最新发展情况...",
                "url": "https://example.com/search1",
                "publishedAt": "2024-01-15T10:30:00Z",
                "source": {"name": "新闻网"}
            },
            {
                "title": f"{query}领域的重要进展",
                "description": f"专家分析{query}未来的发展趋势和影响...",
                "url": "https://example.com/search2",
                "publishedAt": "2024-01-15T09:15:00Z", 
                "source": {"name": "专业媒体"}
            }
        ]
        
        result = f"🔍 搜索结果：'{query}'\n\n"
        
        for i, article in enumerate(mock_results[:count], 1):
            pub_time = article["publishedAt"][:10]
            result += f"{i}. 📰 {article['title']}\n"
            result += f"📅 {pub_time} | 📍 {article['source']['name']}\n"
            result += f"📝 {article['description']}\n"
            result += f"🔗 {article['url']}\n\n"
        
        result += "💡 说明：这是示例搜索结果，实际使用时需要配置真实的新闻搜索API"
        
        return [TextContent(type="text", text=result)]
        
    except Exception as e:
        return [TextContent(type="text", text=f"搜索新闻时出错：{str(e)}")]


async def main():
    """启动MCP服务器"""
    async with stdio_server() as (read_stream, write_stream):
        await app.run(
            read_stream,
            write_stream,
            InitializationOptions(
                server_name="weather-news-mcp",
                server_version="1.0.0",
                capabilities=app.get_capabilities(
                    notification_options=None,
                    experimental_capabilities=None,
                ),
            ),
        )


if __name__ == "__main__":
    asyncio.run(main()) 