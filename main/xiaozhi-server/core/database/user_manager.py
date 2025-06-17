import sqlite3
import threading
import time
from typing import Dict, Any, Optional
from dataclasses import dataclass, asdict
from datetime import datetime
from config.logger import setup_logging

TAG = __name__


@dataclass
class UserInfo:
    """用户信息数据类"""
    user_id: str
    balance: float = 1000.0  # 默认余额1000
    battery: int = 100      # 默认电量100
    created_at: str = None
    updated_at: str = None
    total_requests: int = 0  # 总请求数
    total_cost: float = 0.0  # 总消费
    
    def __post_init__(self):
        if self.created_at is None:
            self.created_at = datetime.now().isoformat()
        if self.updated_at is None:
            self.updated_at = datetime.now().isoformat()
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return asdict(self)


class UserManager:
    """用户信息管理器"""
    
    def __init__(self, db_path: str = "data/users.db"):
        self.db_path = db_path
        self.logger = setup_logging()
        self.lock = threading.Lock()
        self.cost_per_request = 0.5  # 每次请求扣费0.5
        
        # 初始化数据库
        self._init_database()
        
        self.logger.bind(tag=TAG).info(f"用户管理器已初始化 - 数据库路径: {db_path}")
    
    def _init_database(self):
        """初始化数据库表"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                cursor = conn.cursor()
                cursor.execute('''
                    CREATE TABLE IF NOT EXISTS users (
                        user_id TEXT PRIMARY KEY,
                        balance REAL NOT NULL DEFAULT 1000.0,
                        battery INTEGER NOT NULL DEFAULT 100,
                        created_at TEXT NOT NULL,
                        updated_at TEXT NOT NULL,
                        total_requests INTEGER NOT NULL DEFAULT 0,
                        total_cost REAL NOT NULL DEFAULT 0.0
                    )
                ''')
                
                # 创建索引
                cursor.execute('''
                    CREATE INDEX IF NOT EXISTS idx_user_id ON users(user_id)
                ''')
                
                conn.commit()
                self.logger.bind(tag=TAG).info("数据库表初始化成功")
                
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"数据库初始化失败: {str(e)}")
            raise
    
    def get_user(self, user_id: str) -> Optional[UserInfo]:
        """获取用户信息"""
        try:
            with self.lock:
                with sqlite3.connect(self.db_path) as conn:
                    cursor = conn.cursor()
                    cursor.execute('''
                        SELECT user_id, balance, battery, created_at, updated_at, 
                               total_requests, total_cost
                        FROM users WHERE user_id = ?
                    ''', (user_id,))
                    
                    row = cursor.fetchone()
                    if row:
                        return UserInfo(
                            user_id=row[0],
                            balance=row[1],
                            battery=row[2],
                            created_at=row[3],
                            updated_at=row[4],
                            total_requests=row[5],
                            total_cost=row[6]
                        )
                    return None
                    
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"获取用户信息失败: {str(e)}")
            return None
    
    def create_user(self, user_id: str) -> UserInfo:
        """创建新用户"""
        try:
            user_info = UserInfo(user_id=user_id)
            
            with self.lock:
                with sqlite3.connect(self.db_path) as conn:
                    cursor = conn.cursor()
                    cursor.execute('''
                        INSERT INTO users (user_id, balance, battery, created_at, 
                                         updated_at, total_requests, total_cost)
                        VALUES (?, ?, ?, ?, ?, ?, ?)
                    ''', (
                        user_info.user_id,
                        user_info.balance,
                        user_info.battery,
                        user_info.created_at,
                        user_info.updated_at,
                        user_info.total_requests,
                        user_info.total_cost
                    ))
                    conn.commit()
            
            self.logger.bind(tag=TAG).info(f"创建新用户: {user_id}")
            return user_info
            
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"创建用户失败: {str(e)}")
            raise
    
    def get_or_create_user(self, user_id: str) -> UserInfo:
        """获取或创建用户"""
        user = self.get_user(user_id)
        if user is None:
            user = self.create_user(user_id)
        return user
    
    def deduct_balance(self, user_id: str, amount: float = None) -> tuple[bool, UserInfo]:
        """
        扣除用户余额
        
        Args:
            user_id: 用户ID
            amount: 扣除金额，默认为每次请求费用
            
        Returns:
            (是否成功, 用户信息)
        """
        if amount is None:
            amount = self.cost_per_request
        
        try:
            with self.lock:
                current_time = datetime.now().isoformat()
                
                with sqlite3.connect(self.db_path) as conn:
                    cursor = conn.cursor()
                    
                    # 先尝试获取用户
                    cursor.execute('''
                        SELECT user_id, balance, battery, created_at, updated_at, 
                               total_requests, total_cost
                        FROM users WHERE user_id = ?
                    ''', (user_id,))
                    
                    row = cursor.fetchone()
                    
                    if not row:
                        # 用户不存在，创建新用户
                        user_info = UserInfo(user_id=user_id)
                        cursor.execute('''
                            INSERT INTO users (user_id, balance, battery, created_at, 
                                             updated_at, total_requests, total_cost)
                            VALUES (?, ?, ?, ?, ?, ?, ?)
                        ''', (
                            user_info.user_id,
                            user_info.balance,
                            user_info.battery,
                            user_info.created_at,
                            user_info.updated_at,
                            user_info.total_requests,
                            user_info.total_cost
                        ))
                        current_balance = user_info.balance
                        current_requests = user_info.total_requests
                        current_cost = user_info.total_cost
                        self.logger.bind(tag=TAG).info(f"创建新用户: {user_id}")
                    else:
                        current_balance = row[1]
                        current_requests = row[5]
                        current_cost = row[6]
                    
                    # 检查余额是否足够
                    if current_balance < amount:
                        conn.rollback()
                        user = UserInfo(
                            user_id=user_id,
                            balance=current_balance,
                            battery=row[2] if row else 100,
                            created_at=row[3] if row else current_time,
                            updated_at=row[4] if row else current_time,
                            total_requests=current_requests,
                            total_cost=current_cost
                        )
                        self.logger.bind(tag=TAG).warning(f"用户余额不足: {user_id}, 当前余额: {current_balance}, 需要: {amount}")
                        return False, user
                    
                    # 执行扣费
                    new_balance = current_balance - amount
                    new_requests = current_requests + 1
                    new_cost = current_cost + amount
                    
                    cursor.execute('''
                        UPDATE users 
                        SET balance = ?, total_requests = ?, total_cost = ?, updated_at = ?
                        WHERE user_id = ?
                    ''', (new_balance, new_requests, new_cost, current_time, user_id))
                    
                    conn.commit()
                    
                    # 构建返回的用户信息
                    updated_user = UserInfo(
                        user_id=user_id,
                        balance=new_balance,
                        battery=row[2] if row else 100,
                        created_at=row[3] if row else current_time,
                        updated_at=current_time,
                        total_requests=new_requests,
                        total_cost=new_cost
                    )
                    
                    self.logger.bind(tag=TAG).info(
                        f"用户扣费成功: {user_id}, 扣除: {amount}, 剩余: {new_balance}"
                    )
                    
                    return True, updated_user
                
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"扣除余额失败: {str(e)}")
            # 发生错误时返回当前用户信息
            user = self.get_user(user_id)
            if not user:
                user = UserInfo(user_id=user_id)
            return False, user
    
    def update_battery(self, user_id: str, battery: int) -> bool:
        """更新用户电量"""
        try:
            with self.lock:
                current_time = datetime.now().isoformat()
                
                with sqlite3.connect(self.db_path) as conn:
                    cursor = conn.cursor()
                    cursor.execute('''
                        UPDATE users 
                        SET battery = ?, updated_at = ?
                        WHERE user_id = ?
                    ''', (battery, current_time, user_id))
                    conn.commit()
                
                if cursor.rowcount > 0:
                    self.logger.bind(tag=TAG).info(f"更新用户电量: {user_id}, 电量: {battery}%")
                    return True
                else:
                    self.logger.bind(tag=TAG).warning(f"用户不存在: {user_id}")
                    return False
                    
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"更新电量失败: {str(e)}")
            return False
    
    def add_balance(self, user_id: str, amount: float) -> bool:
        """给用户充值余额"""
        try:
            with self.lock:
                current_time = datetime.now().isoformat()
                
                with sqlite3.connect(self.db_path) as conn:
                    cursor = conn.cursor()
                    cursor.execute('''
                        UPDATE users 
                        SET balance = balance + ?, updated_at = ?
                        WHERE user_id = ?
                    ''', (amount, current_time, user_id))
                    conn.commit()
                
                if cursor.rowcount > 0:
                    self.logger.bind(tag=TAG).info(f"用户充值成功: {user_id}, 充值: {amount}")
                    return True
                else:
                    # 用户不存在，创建用户并设置余额
                    user = self.create_user(user_id)
                    user.balance += amount
                    self._update_user_balance(user_id, user.balance)
                    return True
                    
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"充值余额失败: {str(e)}")
            return False
    
    def _update_user_balance(self, user_id: str, balance: float):
        """内部方法：更新用户余额"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute('''
                UPDATE users SET balance = ?, updated_at = ? WHERE user_id = ?
            ''', (balance, datetime.now().isoformat(), user_id))
            conn.commit()
    
    def get_all_users(self) -> list[UserInfo]:
        """获取所有用户信息"""
        try:
            with self.lock:
                with sqlite3.connect(self.db_path) as conn:
                    cursor = conn.cursor()
                    cursor.execute('''
                        SELECT user_id, balance, battery, created_at, updated_at,
                               total_requests, total_cost
                        FROM users 
                        ORDER BY total_requests DESC
                    ''')
                    
                    users = []
                    for row in cursor.fetchall():
                        users.append(UserInfo(
                            user_id=row[0],
                            balance=row[1],
                            battery=row[2],
                            created_at=row[3],
                            updated_at=row[4],
                            total_requests=row[5],
                            total_cost=row[6]
                        ))
                    
                    return users
                    
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"获取所有用户失败: {str(e)}")
            return []
    
    def get_stats(self) -> Dict[str, Any]:
        """获取用户统计信息"""
        try:
            with self.lock:
                with sqlite3.connect(self.db_path) as conn:
                    cursor = conn.cursor()
                    
                    # 总用户数
                    cursor.execute('SELECT COUNT(*) FROM users')
                    total_users = cursor.fetchone()[0]
                    
                    # 总请求数
                    cursor.execute('SELECT SUM(total_requests) FROM users')
                    total_requests = cursor.fetchone()[0] or 0
                    
                    # 总收入
                    cursor.execute('SELECT SUM(total_cost) FROM users')
                    total_revenue = cursor.fetchone()[0] or 0.0
                    
                    # 平均余额
                    cursor.execute('SELECT AVG(balance) FROM users')
                    avg_balance = cursor.fetchone()[0] or 0.0
                    
                    return {
                        "total_users": total_users,
                        "total_requests": total_requests,
                        "total_revenue": round(total_revenue, 2),
                        "average_balance": round(avg_balance, 2),
                        "cost_per_request": self.cost_per_request
                    }
                    
        except Exception as e:
            self.logger.bind(tag=TAG).error(f"获取统计信息失败: {str(e)}")
            return {}


# 全局用户管理器实例
_user_manager_instance = None


def get_user_manager() -> UserManager:
    """获取全局用户管理器实例"""
    global _user_manager_instance
    if _user_manager_instance is None:
        _user_manager_instance = UserManager()
    return _user_manager_instance 