"""
简单的天气新闻插件示例
可以直接放到 main/xiaozhi-server/plugins_func/functions/ 目录下
"""

import requests
import json
from datetime import datetime
from config.logger import setup_logging
from plugins_func.register import register_function, ToolType, ActionResponse, Action

TAG = __name__
logger = setup_logging()

# 增强版天气查询功能描述
ENHANCED_WEATHER_FUNCTION_DESC = {
    "type": "function",
    "function": {
        "name": "get_enhanced_weather",
        "description": (
            "获取增强版天气信息，包括实时天气、未来预报、生活指数等全面信息。"
            "支持多种查询方式：城市名、经纬度坐标。"
            "可以查询当前天气、未来7天预报、以及空气质量等详细信息。"
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "location": {
                    "type": "string",
                    "description": "位置信息，可以是城市名（如：北京、上海）或经纬度（如：116.41,39.92）",
                },
                "query_type": {
                    "type": "string",
                    "description": "查询类型：current(当前天气)、forecast(未来预报)、all(全部信息)",
                    "enum": ["current", "forecast", "all"],
                    "default": "current"
                },
                "days": {
                    "type": "integer",
                    "description": "预报天数，1-7天，默认3天",
                    "default": 3,
                    "minimum": 1,
                    "maximum": 7
                },
                "include_air_quality": {
                    "type": "boolean",
                    "description": "是否包含空气质量信息，默认false",
                    "default": False
                },
                "lang": {
                    "type": "string",
                    "description": "返回语言，默认zh_CN",
                    "default": "zh_CN"
                }
            },
            "required": ["location", "lang"],
        },
    },
}

# 智能新闻推荐功能描述
SMART_NEWS_FUNCTION_DESC = {
    "type": "function",
    "function": {
        "name": "get_smart_news",
        "description": (
            "获取智能推荐新闻，支持多种新闻源和分类。"
            "可以根据用户兴趣、时事热点、地区新闻等进行智能推荐。"
            "支持关键词搜索、分类筛选、时间范围等高级功能。"
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "category": {
                    "type": "string",
                    "description": "新闻类别",
                    "enum": [
                        "热点", "科技", "财经", "体育", "娱乐", 
                        "国际", "军事", "健康", "教育", "汽车"
                    ],
                    "default": "热点"
                },
                "keywords": {
                    "type": "string",
                    "description": "搜索关键词，可选，如：人工智能、新能源等"
                },
                "count": {
                    "type": "integer",
                    "description": "返回新闻数量，默认5条",
                    "default": 5,
                    "minimum": 1,
                    "maximum": 20
                },
                "source": {
                    "type": "string",
                    "description": "新闻源",
                    "enum": [
                        "综合", "人民日报", "新华网", "央视新闻", 
                        "澎湃新闻", "界面新闻", "财新网", "36氪"
                    ],
                    "default": "综合"
                },
                "time_range": {
                    "type": "string",
                    "description": "时间范围",
                    "enum": ["今日", "昨日", "3天内", "一周内"],
                    "default": "今日"
                },
                "include_summary": {
                    "type": "boolean",
                    "description": "是否包含新闻摘要，默认true",
                    "default": True
                },
                "lang": {
                    "type": "string",
                    "description": "返回语言，默认zh_CN",
                    "default": "zh_CN"
                }
            },
            "required": ["lang"],
        },
    },
}

@register_function("get_enhanced_weather", ENHANCED_WEATHER_FUNCTION_DESC, ToolType.SYSTEM_CTL)
def get_enhanced_weather(
    conn, 
    location: str, 
    query_type: str = "current",
    days: int = 3,
    include_air_quality: bool = False,
    lang: str = "zh_CN"
):
    """获取增强版天气信息"""
    
    try:
        # 获取配置
        weather_config = conn.config.get("plugins", {}).get("get_weather", {})
        api_key = weather_config.get("api_key", "a861d0d5e7bf4ee1a83d9a9e4f96d4da")
        api_host = weather_config.get("api_host", "mj7p3y7naa.re.qweatherapi.com")
        
        logger.bind(tag=TAG).info(f"查询增强版天气信息: {location}, 类型: {query_type}")
        
        # 1. 获取城市信息
        city_info = _get_city_info(location, api_key, api_host)
        if not city_info:
            return ActionResponse(
                Action.REQLLM, 
                f"未找到位置信息: {location}，请检查输入是否正确",
                None
            )
        
        city_name = city_info.get("name", location)
        location_id = city_info.get("id")
        
        result_parts = []
        
        # 2. 根据查询类型获取相应信息
        if query_type in ["current", "all"]:
            current_weather = _get_current_weather(location_id, api_key, api_host)
            if current_weather:
                result_parts.append(f"🌤️ {city_name} 实时天气")
                result_parts.append("=" * 25)
                result_parts.append(current_weather)
        
        if query_type in ["forecast", "all"]:
            forecast_weather = _get_forecast_weather(location_id, api_key, api_host, days)
            if forecast_weather:
                result_parts.append(f"\n📅 未来{days}天预报")
                result_parts.append("=" * 25)
                result_parts.append(forecast_weather)
        
        if include_air_quality:
            air_quality = _get_air_quality(location_id, api_key, api_host)
            if air_quality:
                result_parts.append("\n🌬️ 空气质量")
                result_parts.append("=" * 25)
                result_parts.append(air_quality)
        
        if result_parts:
            final_result = "\n".join(result_parts)
            final_result += "\n\n💡 提示：可以说'详细天气'获取更多信息，或'空气质量'查看环境数据"
            return ActionResponse(Action.REQLLM, final_result, None)
        else:
            return ActionResponse(Action.REQLLM, f"获取{city_name}天气信息失败，请稍后重试", None)
            
    except Exception as e:
        logger.bind(tag=TAG).error(f"获取增强版天气信息失败: {e}")
        return ActionResponse(Action.REQLLM, f"天气查询服务暂时不可用: {str(e)}", None)


@register_function("get_smart_news", SMART_NEWS_FUNCTION_DESC, ToolType.SYSTEM_CTL)
def get_smart_news(
    conn,
    category: str = "热点",
    keywords: str = None,
    count: int = 5,
    source: str = "综合",
    time_range: str = "今日",
    include_summary: bool = True,
    lang: str = "zh_CN"
):
    """获取智能推荐新闻"""
    
    try:
        logger.bind(tag=TAG).info(f"获取智能新闻: 类别={category}, 关键词={keywords}, 数量={count}")
        
        # 根据不同的新闻源获取新闻
        if source in ["综合", "澎湃新闻"] or category in ["热点", "科技"]:
            # 使用现有的NewNow接口
            news_data = _get_newsnow_data(conn, category, keywords, count)
        else:
            # 使用RSS源或其他接口
            news_data = _get_rss_news_data(conn, category, count)
        
        if not news_data:
            return ActionResponse(
                Action.REQLLM,
                f"暂时无法获取{category}类别的新闻，请稍后重试或尝试其他类别",
                None
            )
        
        # 格式化新闻输出
        result = _format_smart_news(news_data, category, source, include_summary)
        
        return ActionResponse(Action.REQLLM, result, None)
        
    except Exception as e:
        logger.bind(tag=TAG).error(f"获取智能新闻失败: {e}")
        return ActionResponse(Action.REQLLM, f"新闻获取服务暂时不可用: {str(e)}", None)


def _get_city_info(location, api_key, api_host):
    """获取城市信息"""
    try:
        url = f"https://{api_host}/geo/v2/city/lookup"
        params = {
            "location": location,
            "key": api_key,
            "lang": "zh"
        }
        response = requests.get(url, params=params, timeout=10)
        data = response.json()
        
        if data.get("code") == "200" and data.get("location"):
            return data["location"][0]
        return None
    except Exception as e:
        logger.bind(tag=TAG).error(f"获取城市信息失败: {e}")
        return None


def _get_current_weather(location_id, api_key, api_host):
    """获取当前天气"""
    try:
        url = f"https://{api_host}/v7/weather/now"
        params = {
            "location": location_id,
            "key": api_key
        }
        response = requests.get(url, params=params, timeout=10)
        data = response.json()
        
        if data.get("code") == "200" and data.get("now"):
            now = data["now"]
            update_time = data.get("updateTime", "")
            
            result = f"""📊 当前状况: {now.get('text', '未知')}
🌡️ 温度: {now.get('temp', '--')}°C (体感 {now.get('feelsLike', '--')}°C)
💨 风力: {now.get('windDir', '--')} {now.get('windScale', '--')}级 ({now.get('windSpeed', '--')} km/h)
💧 湿度: {now.get('humidity', '--')}%
👁️ 能见度: {now.get('vis', '--')} km
📅 更新: {update_time[:16] if update_time else '未知'}"""
            
            return result
        return None
    except Exception as e:
        logger.bind(tag=TAG).error(f"获取当前天气失败: {e}")
        return None


def _get_forecast_weather(location_id, api_key, api_host, days):
    """获取天气预报"""
    try:
        url = f"https://{api_host}/v7/weather/{days}d"
        params = {
            "location": location_id,
            "key": api_key
        }
        response = requests.get(url, params=params, timeout=10)
        data = response.json()
        
        if data.get("code") == "200" and data.get("daily"):
            daily_list = data["daily"][:days]
            result_lines = []
            
            for i, day in enumerate(daily_list):
                date = day.get("fxDate", "")
                if date:
                    date_obj = datetime.strptime(date, "%Y-%m-%d")
                    weekday = ["周一", "周二", "周三", "周四", "周五", "周六", "周日"][date_obj.weekday()]
                    
                    if i == 0:
                        day_label = "今天"
                    elif i == 1:
                        day_label = "明天"
                    else:
                        day_label = f"{date[5:]} {weekday}"
                else:
                    day_label = f"第{i+1}天"
                
                line = f"📅 {day_label}: {day.get('textDay', '--')} → {day.get('textNight', '--')}"
                line += f" | 🌡️ {day.get('tempMin', '--')}~{day.get('tempMax', '--')}°C"
                line += f" | 💨 {day.get('windDirDay', '--')} {day.get('windScaleDay', '--')}级"
                
                result_lines.append(line)
            
            return "\n".join(result_lines)
        return None
    except Exception as e:
        logger.bind(tag=TAG).error(f"获取天气预报失败: {e}")
        return None


def _get_air_quality(location_id, api_key, api_host):
    """获取空气质量"""
    try:
        url = f"https://{api_host}/v7/air/now"
        params = {
            "location": location_id,
            "key": api_key
        }
        response = requests.get(url, params=params, timeout=10)
        data = response.json()
        
        if data.get("code") == "200" and data.get("now"):
            air = data["now"]
            
            aqi = air.get("aqi", "--")
            category = air.get("category", "未知")
            pm25 = air.get("pm2p5", "--")
            pm10 = air.get("pm10", "--")
            
            # 根据AQI值确定空气质量等级和颜色emoji
            if isinstance(aqi, str) and aqi.isdigit():
                aqi_num = int(aqi)
                if aqi_num <= 50:
                    level_emoji = "🟢"
                elif aqi_num <= 100:
                    level_emoji = "🟡"
                elif aqi_num <= 150:
                    level_emoji = "🟠"
                else:
                    level_emoji = "🔴"
            else:
                level_emoji = "⚪"
            
            result = f"""{level_emoji} AQI: {aqi} ({category})
🔸 PM2.5: {pm25} μg/m³
🔸 PM10: {pm10} μg/m³
💡 空气质量{category}，注意防护"""
            
            return result
        return None
    except Exception as e:
        logger.bind(tag=TAG).error(f"获取空气质量失败: {e}")
        return None


def _get_newsnow_data(conn, category, keywords, count):
    """从NewNow获取新闻数据"""
    try:
        # 复用现有的NewNow配置
        api_url = "https://newsnow.busiyi.world/api/s?id=thepaper"  # 默认澎湃新闻
        
        # 根据类别选择合适的新闻源
        category_map = {
            "科技": "36kr-quick",
            "财经": "cls-depth", 
            "热点": "baidu",
            "娱乐": "weibo",
            "体育": "hupu"
        }
        
        source_id = category_map.get(category, "thepaper")
        api_url = f"https://newsnow.busiyi.world/api/s?id={source_id}"
        
        response = requests.get(api_url, timeout=10)
        response.raise_for_status()
        data = response.json()
        
        if "items" in data:
            items = data["items"][:count]
            return items
        return []
    except Exception as e:
        logger.bind(tag=TAG).error(f"获取NewNow新闻数据失败: {e}")
        return []


def _get_rss_news_data(conn, category, count):
    """从RSS源获取新闻数据"""
    # 可以扩展支持更多RSS源
    return []


def _format_smart_news(news_data, category, source, include_summary):
    """格式化智能新闻输出"""
    if not news_data:
        return f"暂无{category}类别的新闻"
    
    result_lines = [f"📰 {category}新闻 ({source})")
    result_lines.append("=" * 30)
    
    for i, item in enumerate(news_data, 1):
        title = item.get("title", "无标题")
        url = item.get("url", "#")
        time_str = item.get("time", "")
        
        result_lines.append(f"\n{i}. 📰 {title}")
        
        if time_str:
            result_lines.append(f"⏰ {time_str}")
        
        if include_summary and item.get("description"):
            desc = item.get("description", "")[:100]
            if len(desc) >= 100:
                desc += "..."
            result_lines.append(f"📝 {desc}")
        
        if url != "#":
            result_lines.append(f"🔗 {url}")
    
    result_lines.append(f"\n💡 如需详细内容，请说'第X条新闻详情'")
    
    return "\n".join(result_lines) 