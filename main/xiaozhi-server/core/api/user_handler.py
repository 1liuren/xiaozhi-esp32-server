import json
import asyncio
from aiohttp import web
from core.database.user_manager import get_user_manager
from config.logger import setup_logging

TAG = __name__


class UserHandler:
    """用户信息API处理器"""
    
    def __init__(self, config: dict):
        self.config = config
        self.logger = setup_logging()
        self.user_manager = get_user_manager()
        
    async def handle_get_user(self, request):
        """获取用户信息 - GET /users/{user_id}"""
        try:
            user_id = request.match_info.get('user_id')
            
            if not user_id:
                return web.json_response({
                    "error": "用户ID不能为空",
                    "status": "invalid_param"
                }, status=400)
            
            # 异步获取用户信息
            loop = asyncio.get_event_loop()
            user = await loop.run_in_executor(None, self.user_manager.get_user, user_id)
            
            if user is None:
                return web.json_response({
                    "error": "用户不存在",
                    "status": "user_not_found"
                }, status=404)
            
            return web.json_response({
                "status": "success",
                "data": user.to_dict()
            })
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"获取用户信息失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500)
    
    async def handle_get_all_users(self, request):
        """获取所有用户信息 - GET /users"""
        try:
            loop = asyncio.get_event_loop()
            users = await loop.run_in_executor(None, self.user_manager.get_all_users)
            
            users_data = [user.to_dict() for user in users]
            
            return web.json_response({
                "status": "success",
                "data": users_data,
                "count": len(users_data)
            })
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"获取所有用户失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500)
    
    async def handle_create_user(self, request):
        """创建用户 - POST /users"""
        try:
            data = await request.json()
            user_id = data.get('user_id')
            
            if not user_id:
                return web.json_response({
                    "error": "用户ID不能为空",
                    "status": "invalid_param"
                }, status=400)
            
            # 异步检查用户是否已存在
            loop = asyncio.get_event_loop()
            existing_user = await loop.run_in_executor(None, self.user_manager.get_user, user_id)
            if existing_user:
                return web.json_response({
                    "error": "用户已存在",
                    "status": "user_exists",
                    "data": existing_user.to_dict()
                }, status=409)
            
            # 异步创建新用户
            user = await loop.run_in_executor(None, self.user_manager.create_user, user_id)
            
            return web.json_response({
                "status": "success",
                "message": "用户创建成功",
                "data": user.to_dict()
            }, status=201)
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"创建用户失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500)
    
    async def handle_recharge(self, request):
        """用户充值 - POST /users/{user_id}/recharge"""
        try:
            user_id = request.match_info.get('user_id')
            data = await request.json()
            amount = data.get('amount')
            
            if not user_id:
                return web.json_response({
                    "error": "用户ID不能为空",
                    "status": "invalid_param"
                }, status=400)
            
            if not amount or amount <= 0:
                return web.json_response({
                    "error": "充值金额必须大于0",
                    "status": "invalid_amount"
                }, status=400)
            
            # 异步执行充值
            loop = asyncio.get_event_loop()
            success = await loop.run_in_executor(None, self.user_manager.add_balance, user_id, amount)
            
            if success:
                user = await loop.run_in_executor(None, self.user_manager.get_user, user_id)
                return web.json_response({
                    "status": "success",
                    "message": f"充值成功，充值金额: {amount}",
                    "data": user.to_dict() if user else None
                })
            else:
                return web.json_response({
                    "error": "充值失败",
                    "status": "recharge_failed"
                }, status=500)
                
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"用户充值失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500)
    
    async def handle_update_battery(self, request):
        """更新用户电量 - POST /users/{user_id}/battery"""
        try:
            user_id = request.match_info.get('user_id')
            data = await request.json()
            battery = data.get('battery')
            
            if not user_id:
                return web.json_response({
                    "error": "用户ID不能为空",
                    "status": "invalid_param"
                }, status=400)
            
            if battery is None or not (0 <= battery <= 100):
                return web.json_response({
                    "error": "电量值必须在0-100之间",
                    "status": "invalid_battery"
                }, status=400)
            
            # 异步更新电量
            loop = asyncio.get_event_loop()
            success = await loop.run_in_executor(None, self.user_manager.update_battery, user_id, battery)
            
            if success:
                user = await loop.run_in_executor(None, self.user_manager.get_user, user_id)
                return web.json_response({
                    "status": "success",
                    "message": f"电量更新成功: {battery}%",
                    "data": user.to_dict() if user else None
                })
            else:
                return web.json_response({
                    "error": "电量更新失败",
                    "status": "update_failed"
                }, status=500)
                
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"更新电量失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500)
    
    async def handle_get_stats(self, request):
        """获取用户统计信息 - GET /users/stats"""
        try:
            loop = asyncio.get_event_loop()
            stats = await loop.run_in_executor(None, self.user_manager.get_stats)
            
            return web.json_response({
                "status": "success",
                "data": stats
            })
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"获取统计信息失败: {str(e)}")
            return web.json_response({
                "error": str(e),
                "status": "error"
            }, status=500)
    
    async def handle_options(self, request):
        """处理CORS预检请求"""
        return web.Response(
            headers={
                'Access-Control-Allow-Origin': '*',
                'Access-Control-Allow-Methods': 'GET, POST, PUT, DELETE, OPTIONS',
                'Access-Control-Allow-Headers': 'Content-Type, Authorization',
            }
        ) 