import time
import json
import asyncio
import threading
from typing import Dict, Any, List, Optional
from dataclasses import dataclass
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor
from config.logger import setup_logging

TAG = __name__


@dataclass
class RequestInfo:
    """请求信息数据类"""
    timestamp: float
    client_ip: str
    device_id: str
    session_id: str
    message_type: str
    message_content: Any
    request_id: str
    headers: Dict[str, str]
    user_agent: str = ""
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典格式"""
        return {
            "timestamp": self.timestamp,
            "datetime": datetime.fromtimestamp(self.timestamp).isoformat(),
            "client_ip": self.client_ip,
            "device_id": self.device_id,
            "session_id": self.session_id,
            "message_type": self.message_type,
            "message_content": str(self.message_content)[:1000],  # 限制长度避免日志过大
            "request_id": self.request_id,
            "headers": self.headers,
            "user_agent": self.user_agent
        }


class MessageInterceptor:
    """消息拦截器 - 用于截获和处理所有WebSocket消息"""
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = setup_logging()
        self.enabled = config.get("request_interceptor", {}).get("enabled", True)
        self.log_requests = config.get("request_interceptor", {}).get("log_requests", True)
        self.max_workers = config.get("request_interceptor", {}).get("max_workers", 10)
        
        # 统计信息
        self.total_requests = 0
        self.requests_per_second = 0
        self.start_time = time.time()
        
        # 请求存储（内存中保存最近的请求）
        self.recent_requests: List[RequestInfo] = []
        self.max_recent_requests = 1000  # 最多保存1000条最近请求
        self.lock = threading.Lock()
        
        # 线程池用于异步处理
        self.executor = ThreadPoolExecutor(max_workers=self.max_workers)
        
        # 自定义处理器列表
        self.custom_handlers = []
        
        self.logger.bind(tag=TAG).info(f"消息拦截器已初始化 - 启用状态: {self.enabled}")
    
    async def intercept_message(self, conn, message) -> Any:
        """
        拦截消息的主方法
        
        Args:
            conn: 连接对象
            message: 消息内容（可以是str、bytes等）
            
        Returns:
            处理后的消息（通常返回原消息，除非需要修改）
        """
        if not self.enabled:
            return message
        
        try:
            # 生成请求信息
            request_info = self._create_request_info(conn, message)
            
            # 更新统计信息
            self._update_stats()
            
            # 异步处理请求（不阻塞主流程）
            asyncio.create_task(self._process_request_async(request_info))
            
            # 记录日志
            if self.log_requests:
                self._log_request(request_info)
            
            # 存储到最近请求列表
            self._store_recent_request(request_info)
            
            # 🔥 在这里调用您的自定义处理逻辑
            await self._call_custom_handlers(request_info, message)
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"消息拦截处理失败: {str(e)}")
        
        return message
    
    def _create_request_info(self, conn, message) -> RequestInfo:
        """创建请求信息对象"""
        import uuid
        
        # 确定消息类型
        if isinstance(message, str):
            message_type = "text"
            try:
                msg_json = json.loads(message)
                message_type = f"text_{msg_json.get('type', 'unknown')}"
            except:
                pass
        elif isinstance(message, bytes):
            message_type = "audio"
        else:
            message_type = "unknown"
        
        return RequestInfo(
            timestamp=time.time(),
            client_ip=getattr(conn, 'client_ip', 'unknown'),
            device_id=getattr(conn, 'device_id', 'unknown'),
            session_id=getattr(conn, 'session_id', 'unknown'),
            message_type=message_type,
            message_content=message,
            request_id=str(uuid.uuid4()),
            headers=getattr(conn, 'headers', {}),
            user_agent=getattr(conn, 'headers', {}).get('user-agent', '')
        )
    
    def _update_stats(self):
        """更新统计信息"""
        with self.lock:
            self.total_requests += 1
            current_time = time.time()
            elapsed = current_time - self.start_time
            if elapsed > 0:
                self.requests_per_second = self.total_requests / elapsed
    
    async def _process_request_async(self, request_info: RequestInfo):
        """异步处理请求（在后台线程中执行）"""
        try:
            # 在后台线程中执行处理逻辑，避免阻塞主流程
            loop = asyncio.get_event_loop()
            await loop.run_in_executor(
                self.executor, 
                self._process_request_sync, 
                request_info
            )
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"异步处理请求失败: {str(e)}")
    
    def _process_request_sync(self, request_info: RequestInfo):
        """同步处理请求（在后台线程中执行）"""
        try:
            # 🔥 在这里添加您的自定义处理逻辑
            # 例如：
            # - 保存到数据库
            # - 发送到消息队列
            # - 调用外部API
            # - 数据分析和统计
            
            # 示例：打印请求信息
            if self.config.get("request_interceptor", {}).get("debug", False):
                print(f"处理请求: {request_info.to_dict()}")
            
            # 示例：特殊消息处理
            if request_info.message_type.startswith("text_"):
                self._handle_text_message(request_info)
            elif request_info.message_type == "audio":
                self._handle_audio_message(request_info)
                
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"同步处理请求失败: {str(e)}")
    
    def _handle_text_message(self, request_info: RequestInfo):
        """处理文本消息"""
        # 🔥 在这里添加文本消息的特殊处理逻辑
        try:
            if isinstance(request_info.message_content, str):
                msg_json = json.loads(request_info.message_content)
                
                # 根据消息类型进行不同处理
                if msg_json.get("type") == "listen":
                    self.logger.bind(tag=TAG).info(f"用户开始/停止说话: {request_info.device_id}")
                elif msg_json.get("type") == "hello":
                    self.logger.bind(tag=TAG).info(f"用户连接: {request_info.device_id}")
                
                # 提取用户实际说话内容
                if msg_json.get("type") == "listen" and "text" in msg_json:
                    user_text = msg_json["text"]
                    self.logger.bind(tag=TAG).info(f"用户说话内容: {user_text}")
                    # 🔥 这里是用户实际说话内容，您可以进行进一步处理
                    
        except Exception as e:
            self.logger.bind(tag=TAG).debug(f"处理文本消息失败: {str(e)}")
    
    def _handle_audio_message(self, request_info: RequestInfo):
        """处理音频消息"""
        # 🔥 在这里添加音频消息的特殊处理逻辑
        if isinstance(request_info.message_content, bytes):
            audio_size = len(request_info.message_content)
            self.logger.bind(tag=TAG).debug(f"收到音频数据: {audio_size} bytes from {request_info.device_id}")
    
    def _log_request(self, request_info: RequestInfo):
        """记录请求日志"""
        self.logger.bind(tag=TAG).info(
            f"截获请求 - IP: {request_info.client_ip}, "
            f"设备: {request_info.device_id}, "
            f"类型: {request_info.message_type}, "
            f"时间: {datetime.fromtimestamp(request_info.timestamp).strftime('%H:%M:%S')}"
        )
    
    def _store_recent_request(self, request_info: RequestInfo):
        """存储最近的请求到内存中"""
        with self.lock:
            self.recent_requests.append(request_info)
            # 保持列表大小
            if len(self.recent_requests) > self.max_recent_requests:
                self.recent_requests.pop(0)
    
    async def _call_custom_handlers(self, request_info: RequestInfo, message: Any):
        """调用自定义处理器"""
        for handler in self.custom_handlers:
            try:
                if asyncio.iscoroutinefunction(handler):
                    await handler(request_info, message)
                else:
                    handler(request_info, message)
            except Exception as e:
                self.logger.bind(tag=TAG).error(f"自定义处理器执行失败: {str(e)}")
    
    def add_custom_handler(self, handler):
        """添加自定义处理器"""
        self.custom_handlers.append(handler)
        self.logger.bind(tag=TAG).info(f"已添加自定义处理器: {handler.__name__}")
    
    def get_stats(self) -> Dict[str, Any]:
        """获取统计信息"""
        with self.lock:
            return {
                "total_requests": self.total_requests,
                "requests_per_second": round(self.requests_per_second, 2),
                "recent_requests_count": len(self.recent_requests),
                "uptime_seconds": round(time.time() - self.start_time, 2),
                "enabled": self.enabled
            }
    
    def get_recent_requests(self, limit: int = 100) -> List[Dict[str, Any]]:
        """获取最近的请求"""
        with self.lock:
            recent = self.recent_requests[-limit:] if limit > 0 else self.recent_requests
            return [req.to_dict() for req in recent]
    
    def close(self):
        """关闭拦截器"""
        self.executor.shutdown(wait=True)
        self.logger.bind(tag=TAG).info("消息拦截器已关闭")


# 全局拦截器实例
_interceptor_instance = None


def get_interceptor(config: Dict[str, Any] = None) -> MessageInterceptor:
    """获取全局拦截器实例"""
    global _interceptor_instance
    if _interceptor_instance is None and config is not None:
        _interceptor_instance = MessageInterceptor(config)
        
        # 自动注册自定义处理器
        try:
            from .custom_handlers import create_custom_handlers
            handlers = create_custom_handlers(config)
            for handler in handlers:
                _interceptor_instance.add_custom_handler(handler)
        except ImportError:
            pass  # 如果没有自定义处理器文件，忽略
        except Exception as e:
            logger = setup_logging()
            logger.bind(tag=TAG).error(f"注册自定义处理器失败: {str(e)}")
            
    return _interceptor_instance 