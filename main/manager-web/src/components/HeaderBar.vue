<template>
  <el-header class="header">
    <div class="header-container">
      <!-- 左侧元素 -->
      <div class="header-left" @click="goHome">
        <div class="brand-container">
          <div class="brand-icon">🧠</div>
          <div class="brand-text">
            <span class="brand-name">幻话科技</span>
            <span class="brand-subtitle">AI Intelligence</span>
          </div>
        </div>
      </div>

      <!-- 中间导航菜单 -->
      <div class="header-center">
        <div class="nav-menu-container">
          <!-- 核心菜单 -->
          <div class="nav-item primary-nav"
            :class="{ 'active-tab': $route.path === '/home' || $route.path === '/role-config' || $route.path === '/device-management' }"
            @click="goHome">
            <span class="nav-icon">🤖</span>
            <span class="nav-text">AI助手</span>
          </div>
          
          <!-- 管理员菜单 -->
          <template v-if="isSuperAdmin">
            <div class="nav-item"
              :class="{ 'active-tab': $route.path === '/model-config' }"
              @click="goModelConfig">
              <span class="nav-icon">⚙️</span>
              <span class="nav-text">模型</span>
            </div>
            
            <div class="nav-item"
              :class="{ 'active-tab': $route.path === '/user-management' }"
              @click="goUserManagement">
              <span class="nav-icon">👥</span>
              <span class="nav-text">用户</span>
            </div>
            
            <div class="nav-item"
              :class="{ 'active-tab': $route.path === '/ota-management' }"
              @click="goOtaManagement">
              <span class="nav-icon">🔄</span>
              <span class="nav-text">更新</span>
            </div>
            
            <el-dropdown trigger="click" class="nav-item nav-dropdown"
              :class="{ 'active-tab': $route.path === '/dict-management' || $route.path === '/params-management' || $route.path === '/provider-management' || $route.path === '/server-side-management' }"
              @visible-change="handleParamDropdownVisibleChange">
              <span class="el-dropdown-link">
                <span class="nav-icon">📊</span>
                <span class="nav-text">系统</span>
                <i class="el-icon-arrow-down" :class="{ 'rotate-down': paramDropdownVisible }"></i>
              </span>
              <el-dropdown-menu slot="dropdown">
                <el-dropdown-item @click.native="goParamManagement">
                  <span class="dropdown-icon">⚙️</span>
                  参数管理
                </el-dropdown-item>
                <el-dropdown-item @click.native="goDictManagement">
                  <span class="dropdown-icon">📖</span>
                  字典管理
                </el-dropdown-item>
                <el-dropdown-item @click.native="goProviderManagement">
                  <span class="dropdown-icon">🔧</span>
                  字段管理
                </el-dropdown-item>
                <el-dropdown-item @click.native="goServerSideManagement">
                  <span class="dropdown-icon">🖥️</span>
                  服务端管理
                </el-dropdown-item>
              </el-dropdown-menu>
            </el-dropdown>
          </template>
        </div>
      </div>

      <!-- 右侧元素 -->
      <div class="header-right">
        <div class="search-container" v-if="$route.path === '/home' && !(isSuperAdmin && isSmallScreen)">
          <el-input v-model="search" placeholder="输入名称搜索.." class="custom-search-input"
            @keyup.enter.native="handleSearch">
            <i slot="suffix" class="el-icon-search search-icon" @click="handleSearch"></i>
          </el-input>
        </div>
        <img loading="lazy" alt="" src="@/assets/home/avatar.png" class="avatar-img" />
        <el-dropdown trigger="click" class="user-dropdown" @visible-change="handleUserDropdownVisibleChange">
          <span class="el-dropdown-link">
            {{ userInfo.username || '加载中...' }}
            <i class="el-icon-arrow-down el-icon--right" :class="{ 'rotate-down': userDropdownVisible }"></i>
          </span>
          <el-dropdown-menu slot="dropdown">
            <el-dropdown-item @click.native="showChangePasswordDialog">修改密码</el-dropdown-item>
            <el-dropdown-item @click.native="handleLogout">退出登录</el-dropdown-item>
          </el-dropdown-menu>
        </el-dropdown>
      </div>
    </div>

    <!-- 修改密码弹窗 -->
    <ChangePasswordDialog v-model="isChangePasswordDialogVisible" />
  </el-header>
</template>

<script>
import userApi from '@/apis/module/user';
import { mapActions, mapGetters } from 'vuex';
import ChangePasswordDialog from './ChangePasswordDialog.vue'; // 引入修改密码弹窗组件

export default {
  name: 'HeaderBar',
  components: {
    ChangePasswordDialog
  },
  props: ['devices'],  // 接收父组件设备列表
  data() {
    return {
      search: '',
      userInfo: {
        username: '',
        mobile: ''
      },
      isChangePasswordDialogVisible: false, // 控制修改密码弹窗的显示
      userDropdownVisible: false,
      paramDropdownVisible: false,
      isSmallScreen: false
    }
  },
  computed: {
    ...mapGetters(['getIsSuperAdmin']),
    isSuperAdmin() {
      return this.getIsSuperAdmin;
    }
  },
  mounted() {
    this.fetchUserInfo();
    this.checkScreenSize();
    window.addEventListener('resize', this.checkScreenSize);
  },
  //移除事件监听器
  beforeDestroy() {
    window.removeEventListener('resize', this.checkScreenSize);
  },
  methods: {
    goHome() {
      // 跳转到首页
      this.$router.push('/home')
    },
    goUserManagement() {
      this.$router.push('/user-management')
    },
    goModelConfig() {
      this.$router.push('/model-config')
    },
    goParamManagement() {
      this.$router.push('/params-management')
    },
    goOtaManagement() {
      this.$router.push('/ota-management')
    },
    goDictManagement() {
      this.$router.push('/dict-management')
    },
    goProviderManagement() {
      this.$router.push('/provider-management')
    },
    goServerSideManagement() {
      this.$router.push('/server-side-management')
    },
    // 获取用户信息
    fetchUserInfo() {
      userApi.getUserInfo(({ data }) => {
        this.userInfo = data.data
        if (data.data.superAdmin !== undefined) {
          this.$store.commit('setUserInfo', data.data);
        }
      })
    },
    checkScreenSize() {
      this.isSmallScreen = window.innerWidth <= 1386;
    },
    // 处理搜索
    handleSearch() {
      const searchValue = this.search.trim();

      // 如果搜索内容为空，触发重置事件
      if (!searchValue) {
        this.$emit('search-reset');
        return;
      }

      try {
        // 创建不区分大小写的正则表达式
        const regex = new RegExp(searchValue, 'i');
        // 触发搜索事件，将正则表达式传递给父组件
        this.$emit('search', regex);
      } catch (error) {
        console.error('正则表达式创建失败:', error);
        this.$message.error({
          message: '搜索关键词格式不正确',
          showClose: true
        });
      }
    },
    // 显示修改密码弹窗
    showChangePasswordDialog() {
      this.isChangePasswordDialogVisible = true;
    },
    // 退出登录
    async handleLogout() {
      try {
        // 调用 Vuex 的 logout action
        await this.logout();
        this.$message.success({
          message: '退出登录成功',
          showClose: true
        });
      } catch (error) {
        console.error('退出登录失败:', error);
        this.$message.error({
          message: '退出登录失败，请重试',
          showClose: true
        });
      }
    },
    handleUserDropdownVisibleChange(visible) {
      this.userDropdownVisible = visible;
    },
    // 监听第二个下拉菜单的可见状态变化
    handleParamDropdownVisibleChange(visible) {
      this.paramDropdownVisible = visible;
    },

    // 使用 mapActions 引入 Vuex 的 logout action
    ...mapActions(['logout'])
  }
}
</script>

<style lang="scss" scoped>
.header {
  background: rgba(255, 255, 255, 0.95);
  backdrop-filter: blur(20px);
  border: none;
  box-shadow: 0 2px 20px rgba(0, 0, 0, 0.1);
  height: 70px !important;
  min-width: 900px;
  position: relative;
  z-index: 100;
}

.header-container {
  display: flex;
  justify-content: space-between;
  align-items: center;
  height: 100%;
  padding: 0 20px;
  max-width: 1400px;
  margin: 0 auto;
}

.header-left {
  display: flex;
  align-items: center;
  min-width: 200px;
  cursor: pointer;
}

.brand-container {
  display: flex;
  align-items: center;
  gap: 12px;
  transition: all 0.3s ease;
}

.brand-container:hover {
  transform: scale(1.05);
}

.brand-icon {
  font-size: 28px;
  background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
  width: 45px;
  height: 45px;
  border-radius: 12px;
  display: flex;
  align-items: center;
  justify-content: center;
  box-shadow: 0 4px 15px rgba(102, 126, 234, 0.3);
}

.brand-text {
  display: flex;
  flex-direction: column;
  gap: 2px;
}

.brand-name {
  font-size: 18px;
  font-weight: 700;
  background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
  -webkit-background-clip: text;
  -webkit-text-fill-color: transparent;
  background-clip: text;
  line-height: 1;
}

.brand-subtitle {
  font-size: 11px;
  color: #718096;
  font-weight: 500;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.header-center {
  display: flex;
  align-items: center;
  flex: 1;
  justify-content: center;
  max-width: 900px;
  margin: 0 30px;
  padding: 8px 0;
}

.nav-menu-container {
  display: flex;
  align-items: center;
  gap: 6px;
  background: rgba(255, 255, 255, 0.15);
  backdrop-filter: blur(20px);
  padding: 6px;
  border-radius: 30px;
  border: 1px solid rgba(255, 255, 255, 0.2);
  box-shadow: 0 4px 20px rgba(0, 0, 0, 0.1);
}

.header-right {
  display: flex;
  align-items: center;
  gap: 12px;
  min-width: 300px;
  justify-content: flex-end;
}

.nav-item {
  height: 40px;
  border-radius: 20px;
  background: transparent;
  display: flex;
  justify-content: center;
  font-size: 13px;
  font-weight: 600;
  gap: 6px;
  color: rgba(255, 255, 255, 0.8);
  align-items: center;
  transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1);
  cursor: pointer;
  flex-shrink: 0;
  padding: 0 16px;
  position: relative;
  white-space: nowrap;
  min-width: 80px;
  text-align: center;
}

.nav-item.primary-nav {
  min-width: 100px;
  background: rgba(255, 255, 255, 0.1);
}

.nav-item:hover {
  background: rgba(255, 255, 255, 0.2);
  color: #fff;
  transform: translateY(-1px);
  box-shadow: 0 4px 15px rgba(0, 0, 0, 0.15);
}

.nav-item.active-tab {
  background: linear-gradient(135deg, #ff6b6b 0%, #ee5a24 100%) !important;
  color: #fff !important;
  box-shadow: 0 6px 20px rgba(255, 107, 107, 0.4);
  transform: translateY(-1px);
}

.nav-item.active-tab:hover {
  transform: translateY(-2px);
  box-shadow: 0 8px 25px rgba(255, 107, 107, 0.5);
}

.nav-icon {
  font-size: 16px;
  transition: all 0.3s ease;
  opacity: 0.9;
}

.nav-text {
  font-size: 13px;
  font-weight: 600;
  transition: all 0.3s ease;
}

.nav-item:hover .nav-icon {
  opacity: 1;
  transform: scale(1.1);
}

.nav-item.active-tab .nav-icon {
  opacity: 1;
  animation: pulse 2s infinite;
}

@keyframes pulse {
  0%, 100% { transform: scale(1); }
  50% { transform: scale(1.05); }
}

.search-container {
  margin-right: 15px;
  min-width: 150px;
  flex-grow: 1;
  max-width: 220px;
}

.search-icon {
  cursor: pointer;
  color: #909399;
  margin-right: 8px;
  font-size: 14px;
  line-height: 30px;
}

.avatar-img {
  width: 21px;
  height: 21px;
  flex-shrink: 0;
}

.user-dropdown {
  flex-shrink: 0;
}

.nav-dropdown {
  position: relative;
}

.nav-dropdown .el-dropdown-link {
  display: flex;
  align-items: center;
  gap: 6px;
  width: 100%;
  justify-content: center;
  color: inherit;
  text-decoration: none;
}

.rotate-down {
  transform: rotate(180deg);
  transition: transform 0.3s cubic-bezier(0.4, 0, 0.2, 1);
}

.el-icon-arrow-down {
  transition: transform 0.3s cubic-bezier(0.4, 0, 0.2, 1);
  font-size: 12px;
  opacity: 0.7;
  margin-left: 4px;
}

.nav-item:hover .el-icon-arrow-down {
  opacity: 1;
}

.nav-item.active-tab .el-icon-arrow-down {
  opacity: 1;
  color: white;
}

/* 响应式调整 */
@media (max-width: 1400px) {
  .header-center {
    margin: 0 20px;
  }

  .nav-menu-container {
    gap: 4px;
    padding: 4px;
  }

  .nav-item {
    min-width: 70px;
    padding: 0 14px;
    font-size: 12px;
  }

  .nav-item.primary-nav {
    min-width: 85px;
  }
}

@media (max-width: 1200px) {
  .header-center {
    margin: 0 15px;
  }

  .nav-item {
    min-width: 60px;
    padding: 0 12px;
    font-size: 11px;
    height: 36px;
    border-radius: 18px;
  }

  .nav-item.primary-nav {
    min-width: 75px;
  }

  .nav-icon {
    font-size: 14px;
  }

  .nav-text {
    font-size: 11px;
  }
}

@media (max-width: 1000px) {
  .nav-menu-container {
    gap: 2px;
  }

  .nav-item {
    min-width: 50px;
    padding: 0 10px;
    font-size: 10px;
    height: 32px;
    border-radius: 16px;
  }

  .nav-item.primary-nav {
    min-width: 65px;
  }

  .nav-icon {
    font-size: 12px;
  }

  .nav-text {
    font-size: 10px;
  }
}

@media (max-width: 800px) {
  .nav-item .nav-text {
    display: none;
  }

  .nav-item {
    min-width: 40px;
    padding: 0 8px;
  }

  .nav-item.primary-nav {
    min-width: 45px;
  }
}

.equipment-management.more-dropdown {
  position: relative;
  white-space: nowrap;
}

/* 下拉菜单图标样式 */
.dropdown-icon {
  font-size: 14px;
  margin-right: 8px;
  opacity: 0.8;
}
</style>

<style lang="scss">
/* 全局ElementUI样式 - 不使用scoped */
.custom-search-input .el-input__inner {
  height: 30px;
  border-radius: 15px;
  background-color: #fff;
  border: 1px solid #e4e6ef;
  padding-left: 15px;
  font-size: 12px;
  box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
  width: 100%;
}

.custom-search-input .el-input__suffix-inner {
  display: flex;
  align-items: center;
  height: 100%;
}

/* 全局下拉菜单样式 */
.el-dropdown-menu {
  background: rgba(255, 255, 255, 0.95);
  backdrop-filter: blur(20px);
  border: 1px solid rgba(102, 126, 234, 0.1);
  border-radius: 12px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.1);
  padding: 8px 0;
  margin-top: 8px;
  min-width: 140px;
}

.el-dropdown-menu__item {
  padding: 12px 20px;
  font-size: 13px;
  color: #4a5568;
  font-weight: 500;
  transition: all 0.3s ease;
  border-radius: 0;
  display: flex;
  align-items: center;
}

.el-dropdown-menu__item:hover {
  background: linear-gradient(135deg, #ff6b6b 0%, #ee5a24 100%);
  color: white;
  transform: translateX(4px);
}

.el-dropdown-menu__item:hover .dropdown-icon {
  opacity: 1;
  transform: scale(1.1);
}

.el-dropdown-menu__item:not(:last-child) {
  border-bottom: 1px solid rgba(102, 126, 234, 0.05);
}
</style>