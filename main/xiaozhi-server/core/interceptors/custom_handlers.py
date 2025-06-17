import json
import time
import asyncio
from typing import Dict, Any
from datetime import datetime
from config.logger import setup_logging
from core.database.user_manager import get_user_manager

TAG = __name__


class DatabaseHandler:
    """数据库存储处理器示例"""
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = setup_logging()
        self.enabled = config.get("request_interceptor", {}).get("custom_handlers", {}).get("database_storage", False)
        
    async def handle_request(self, request_info, message):
        """处理请求并存储到数据库"""
        if not self.enabled:
            return
            
        try:
            # 🔥 在这里添加数据库存储逻辑
            # 例如使用SQLAlchemy、PyMongo等
            self.logger.bind(tag=TAG).info(f"存储请求到数据库: {request_info.request_id}")
            
            # 示例：模拟数据库存储
            data = {
                "request_id": request_info.request_id,
                "timestamp": request_info.timestamp,
                "client_ip": request_info.client_ip,
                "device_id": request_info.device_id,
                "message_type": request_info.message_type,
                "created_at": datetime.now().isoformat()
            }
            
            # 这里您可以替换为实际的数据库操作
            # await self.save_to_database(data)
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"数据库存储失败: {str(e)}")


class MessageQueueHandler:
    """消息队列处理器示例"""
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = setup_logging()
        self.enabled = config.get("request_interceptor", {}).get("custom_handlers", {}).get("message_queue", False)
        
    async def handle_request(self, request_info, message):
        """发送请求到消息队列"""
        if not self.enabled:
            return
            
        try:
            # 🔥 在这里添加消息队列逻辑
            # 例如使用RabbitMQ、Redis、Kafka等
            self.logger.bind(tag=TAG).info(f"发送请求到消息队列: {request_info.request_id}")
            
            # 示例：模拟消息队列
            queue_message = {
                "type": "user_request",
                "data": request_info.to_dict(),
                "timestamp": time.time()
            }
            
            # 这里您可以替换为实际的消息队列操作
            # await self.publish_to_queue(queue_message)
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"消息队列发送失败: {str(e)}")


class ExternalApiHandler:
    """外部API调用处理器示例"""
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = setup_logging()
        self.enabled = config.get("request_interceptor", {}).get("custom_handlers", {}).get("external_api", False)
        
    async def handle_request(self, request_info, message):
        """调用外部API"""
        if not self.enabled:
            return
            
        try:
            # 🔥 在这里添加外部API调用逻辑
            self.logger.bind(tag=TAG).info(f"调用外部API: {request_info.request_id}")
            
            # 示例：模拟API调用
            api_data = {
                "event": "user_request",
                "user_id": request_info.device_id,
                "timestamp": request_info.timestamp,
                "message_type": request_info.message_type
            }
            
            # 这里您可以替换为实际的HTTP请求
            # async with aiohttp.ClientSession() as session:
            #     async with session.post("https://your-api.com/webhook", json=api_data) as response:
            #         result = await response.json()
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"外部API调用失败: {str(e)}")


class UserBehaviorAnalyzer:
    """用户行为分析处理器"""
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = setup_logging()
        self.user_sessions = {}  # 存储用户会话信息
        self.user_manager = get_user_manager()  # 用户管理器
        
    async def handle_request(self, request_info, message):
        """分析用户行为"""
        try:
            device_id = request_info.device_id
            
            # 初始化用户会话
            if device_id not in self.user_sessions:
                self.user_sessions[device_id] = {
                    "first_seen": request_info.timestamp,
                    "last_seen": request_info.timestamp,
                    "message_count": 0,
                    "message_types": {},
                    "session_duration": 0
                }
            
            session = self.user_sessions[device_id]
            session["last_seen"] = request_info.timestamp
            session["message_count"] += 1
            session["session_duration"] = request_info.timestamp - session["first_seen"]
            
            # 统计消息类型
            msg_type = request_info.message_type
            session["message_types"][msg_type] = session["message_types"].get(msg_type, 0) + 1
            
            # 🔥 在这里添加您的用户行为分析逻辑
            if session["message_count"] % 10 == 0:  # 每10个消息分析一次
                self.logger.bind(tag=TAG).info(
                    f"用户行为分析 - 设备: {device_id}, "
                    f"消息数: {session['message_count']}, "
                    f"会话时长: {session['session_duration']:.2f}秒"
                )
            
            # 🔥 用户请求扣费逻辑 - 异步执行避免阻塞
            if request_info.message_type.startswith("text_") and isinstance(message, str):
                try:
                    msg_json = json.loads(message)
                    # 只对用户实际的交互进行扣费（排除系统消息）
                    if msg_json.get("type") in ["listen", "hello"]:
                        if msg_json.get("type") == "listen" and msg_json.get("state") == "detect":
                            # 用户发送了实际的对话内容 - 在后台线程执行扣费
                            loop = asyncio.get_event_loop()
                            asyncio.create_task(self._deduct_balance_async(device_id))
                            
                            # 检测用户实际说话内容
                            if "text" in msg_json:
                                user_text = msg_json["text"]
                                # 🔥 这里是用户实际说话的内容
                                self.logger.bind(tag=TAG).info(f"用户说话: [{device_id}] {user_text}")
                                
                                # 您可以在这里进行进一步分析：
                                # - 情感分析
                                # - 关键词提取
                                # - 意图识别
                                # - 语音转文本质量评估
                        
                        elif msg_json.get("type") == "hello":
                            # 用户连接时不扣费，但确保用户存在 - 在后台线程执行
                            loop = asyncio.get_event_loop()
                            asyncio.create_task(self._ensure_user_exists_async(device_id))
                        
                except Exception as e:
                    self.logger.bind(tag=TAG).debug(f"处理用户扣费失败: {str(e)}")
                    
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"用户行为分析失败: {str(e)}")
    
    async def _deduct_balance_async(self, device_id: str):
        """异步执行用户扣费"""
        try:
            loop = asyncio.get_event_loop()
            success, user_info = await loop.run_in_executor(
                None, self.user_manager.deduct_balance, device_id
            )
            
            if success:
                self.logger.bind(tag=TAG).info(
                    f"💰 用户扣费成功: [{device_id}] 扣除: 0.5, 余额: {user_info.balance}"
                )
            else:
                self.logger.bind(tag=TAG).warning(
                    f"💸 用户余额不足: [{device_id}] 当前余额: {user_info.balance}"
                )
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"异步扣费失败: {str(e)}")
    
    async def _ensure_user_exists_async(self, device_id: str):
        """异步确保用户存在"""
        try:
            loop = asyncio.get_event_loop()
            user_info = await loop.run_in_executor(
                None, self.user_manager.get_or_create_user, device_id
            )
            self.logger.bind(tag=TAG).info(
                f"👋 用户连接: [{device_id}] 余额: {user_info.balance}"
            )
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"异步确保用户存在失败: {str(e)}")


# 工厂函数：根据配置创建处理器
def create_custom_handlers(config: Dict[str, Any]) -> list:
    """根据配置创建自定义处理器"""
    handlers = []
    
    # 添加数据库处理器
    if config.get("request_interceptor", {}).get("custom_handlers", {}).get("database_storage", False):
        handlers.append(DatabaseHandler(config).handle_request)
    
    # 添加消息队列处理器
    if config.get("request_interceptor", {}).get("custom_handlers", {}).get("message_queue", False):
        handlers.append(MessageQueueHandler(config).handle_request)
    
    # 添加外部API处理器
    if config.get("request_interceptor", {}).get("custom_handlers", {}).get("external_api", False):
        handlers.append(ExternalApiHandler(config).handle_request)
    
    # 默认添加用户行为分析器
    handlers.append(UserBehaviorAnalyzer(config).handle_request)
    
    return handlers 