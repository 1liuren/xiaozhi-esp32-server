# 小智天气新闻功能使用指南

## 📋 概述

小智系统已经内置了完整的天气和新闻查询功能，支持多种实现方式：

1. **现有内置功能**：已配置好的天气和新闻插件
2. **增强版插件**：更强大的自定义插件
3. **MCP扩展**：通过MCP协议扩展的外部工具

## 🌤️ 天气功能

### 现有天气功能

#### 基础用法
用户可以直接与小智对话：
```
"今天天气怎么样？"
"北京天气如何？"
"告诉我明天的天气"
"广州未来7天天气预报"
```

#### 功能特点
- ✅ **自动定位**：根据IP地址自动识别城市
- ✅ **多城市查询**：支持全国各地城市查询
- ✅ **7天预报**：提供未来一周天气预报
- ✅ **详细信息**：温度、湿度、风力、能见度等
- ✅ **多语言支持**：支持中文、英文等多种语言

#### 配置信息
```yaml
# config.yaml 中的配置
get_weather: 
  api_host: "mj7p3y7naa.re.qweatherapi.com"
  api_key: "a861d0d5e7bf4ee1a83d9a9e4f96d4da"  # 和风天气API
  default_location: "广州"
```

### 增强版天气功能

如果需要更高级的天气功能，可以使用我们提供的增强版插件：

#### 新增功能
- 🌬️ **空气质量**：PM2.5、PM10、AQI指数
- 🎯 **精确查询**：支持经纬度坐标查询
- 📊 **分类显示**：实时/预报/综合信息分类
- 🎨 **美化输出**：更友好的显示格式

#### 使用方法
1. 将`simple_weather_news_plugin.py`放到`plugins_func/functions/`目录
2. 在配置文件中启用该插件
3. 重启服务

## 📰 新闻功能

### 现有新闻功能

#### 基础用法
```
"播报一下最新新闻"
"给我看看百度热搜"
"有什么科技新闻吗？"
"财经新闻有什么？"
```

#### 两个新闻插件

**1. 中新网新闻 (`get_news_from_chinanews`)**
- 📡 RSS源获取
- 🏷️ 支持分类：社会、国际、财经
- 📅 按时间排序
- 🔗 提供原文链接

**2. NewNow聚合新闻 (`get_news_from_newsnow`)**
- 🌐 多源聚合
- 📱 支持热门平台：澎湃新闻、百度热搜、财联社等
- 🎯 实时热点
- 📊 更丰富的内容

#### 配置信息
```yaml
# 中新网新闻配置
get_news_from_chinanews:
  default_rss_url: "https://www.chinanews.com.cn/rss/society.xml"
  society_rss_url: "https://www.chinanews.com.cn/rss/society.xml"
  world_rss_url: "https://www.chinanews.com.cn/rss/world.xml"
  finance_rss_url: "https://www.chinanews.com.cn/rss/finance.xml"

# NewNow新闻配置
get_news_from_newsnow:
  url: "https://newsnow.busiyi.world/api/s?id="
  news_sources: "澎湃新闻;百度热搜;财联社"
```

### 新闻源支持

NewNow插件支持以下新闻源：
- 📰 **主流媒体**：澎湃新闻、参考消息、卫星通讯社
- 💼 **财经类**：华尔街见闻、36氪、财联社、雪球
- 🔧 **科技类**：IT之家、Solidot、Hacker News、稀土掘金
- 🎮 **社交平台**：微博、知乎、虎扑、哔哩哔哩
- 🌍 **国际**：联合早报

## 🚀 MCP扩展方式

### 什么是MCP？

MCP (Model Context Protocol) 是一种标准化的模型上下文协议，允许：
- 🔌 **外部工具集成**：连接第三方服务
- 🛠️ **自定义功能**：开发专属工具
- 🌐 **分布式部署**：工具可独立运行
- 📡 **实时通信**：WebSocket连接

### MCP实现方式

**1. MCP接入点 (推荐)**
- 通过WebSocket连接外部MCP服务
- 配置简单，扩展性强
- 支持多个独立的MCP工具

**2. 服务端MCP**
- 直接在服务端运行MCP服务
- 性能更好，集成更紧密
- 配置相对复杂

**3. 设备端MCP**
- 设备端运行MCP客户端
- 适合IoT设备集成

### 使用MCP的优势

- ✨ **模块化**：功能独立，便于维护
- 🔄 **可扩展**：随时添加新功能
- 🛡️ **安全隔离**：工具间相互独立
- 🌍 **社区生态**：利用现有MCP工具

## 📖 使用指南

### 1. 检查现有功能

首先确认当前配置是否正确：

```bash
# 检查配置文件
cat main/xiaozhi-server/config.yaml | grep -A 10 "plugins:"
```

### 2. 启用所需插件

在`config.yaml`的`Intent.function_call.functions`中确保包含：

```yaml
Intent:
  function_call:
    functions:
      - get_weather          # 天气功能
      - get_news_from_newsnow  # NewNow新闻
      # - get_news_from_chinanews  # 中新网新闻（可选）
```

### 3. 测试功能

启动系统后测试：

```
# 天气测试
"今天天气怎么样？"
"北京的天气预报"

# 新闻测试  
"最新新闻有什么？"
"科技新闻"
"百度热搜"
```

### 4. 添加自定义功能

如需自定义功能：

**方法A：内置插件**
1. 将插件文件放到`plugins_func/functions/`
2. 在配置中启用
3. 重启服务

**方法B：MCP扩展**
1. 部署MCP服务
2. 配置MCP接入点
3. 连接测试

## 🔧 高级配置

### 天气API配置

如需更稳定的天气服务：

1. 注册和风天气账号：https://console.qweather.com/
2. 获取API Key
3. 更新配置文件中的`api_key`

### 新闻源自定义

如需添加新的新闻源：

1. 找到RSS源或API接口
2. 修改插件代码中的`CHANNEL_MAP`
3. 更新配置文件

### MCP工具开发

开发自定义MCP工具：

1. 使用`weather_news_mcp_server.py`作为模板
2. 实现所需的工具函数
3. 部署为独立服务
4. 配置接入点连接

## ❓ 常见问题

**Q: 天气查询失败怎么办？**
A: 检查网络连接和API配置，可能是API限制或密钥过期

**Q: 新闻内容不更新？**
A: 新闻源可能有访问限制，尝试更换新闻源或检查网络

**Q: 如何添加新的城市？**
A: 天气功能支持全国城市，直接说城市名即可

**Q: MCP连接失败？**
A: 检查WebSocket地址是否正确，确保MCP服务正在运行

**Q: 插件不生效？**
A: 确保插件在配置文件中启用，并重启了服务

## 📚 进一步学习

- 📖 [小智官方文档](https://github.com/xinnan-tech/xiaozhi-esp32-server)
- 🔧 [MCP协议文档](https://modelcontextprotocol.io/)
- 🌤️ [和风天气API](https://dev.qweather.com/)
- 📰 [RSS新闻源](https://www.chinanews.com.cn/rss/)

---

**享受与小智的智能对话体验！** 🎉 