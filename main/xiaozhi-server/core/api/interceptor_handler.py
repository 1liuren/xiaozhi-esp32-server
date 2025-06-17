import json
from aiohttp import web
from core.interceptors.message_interceptor import get_interceptor
from config.logger import setup_logging
import time

TAG = __name__


class InterceptorHandler:
    """拦截器监控API处理器"""
    
    def __init__(self, config: dict):
        self.config = config
        self.logger = setup_logging()
        
    async def handle_get(self, request):
        """处理GET请求 - 获取拦截器状态"""
        try:
            interceptor = get_interceptor()
            
            if not interceptor:
                return web.json_response({
                    "error": "拦截器未初始化",
                    "status": "not_initialized"
                }, status=404)
            
            # 获取统计信息
            stats = interceptor.get_stats()
            
            # 获取最近的请求（可选参数limit）
            limit = int(request.query.get('limit', 10))
            recent_requests = interceptor.get_recent_requests(limit)
            
            response_data = {
                "status": "success",
                "interceptor_stats": stats,
                "recent_requests": recent_requests,
                "config": {
                    "enabled": interceptor.enabled,
                    "log_requests": interceptor.log_requests,
                    "max_workers": interceptor.max_workers
                }
            }
            
            return web.json_response(response_data)
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"获取拦截器状态失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500)
    
    async def handle_post(self, request):
        """处理POST请求 - 控制拦截器"""
        try:
            data = await request.json()
            action = data.get("action")
            
            interceptor = get_interceptor()
            if not interceptor:
                return web.json_response({
                    "error": "拦截器未初始化",
                    "status": "not_initialized"
                }, status=404)
            
            if action == "enable":
                interceptor.enabled = True
                message = "拦截器已启用"
            elif action == "disable":
                interceptor.enabled = False
                message = "拦截器已禁用"
            elif action == "clear_recent":
                with interceptor.lock:
                    interceptor.recent_requests.clear()
                message = "最近请求记录已清空"
            elif action == "reset_stats":
                with interceptor.lock:
                    interceptor.total_requests = 0
                    interceptor.requests_per_second = 0
                    interceptor.start_time = time.time()
                message = "统计信息已重置"
            else:
                return web.json_response({
                    "error": "不支持的操作",
                    "status": "unsupported_action"
                }, status=400)
            
            return web.json_response({
                "status": "success",
                "message": message,
                "current_stats": interceptor.get_stats()
            })
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"控制拦截器失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500) 