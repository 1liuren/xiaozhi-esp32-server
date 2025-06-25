<template>
  <div class="welcome">
    <!-- 公共头部 -->
    <HeaderBar :devices="devices" @search="handleSearch" @search-reset="handleSearchReset" />
    
    <!-- 主要内容区 -->
    <div class="main-content">
      <!-- 欢迎横幅区域 -->
      <div class="hero-banner">
        <div class="hero-content">
          <div class="hero-left">
            <div class="greeting-section">
              <h1 class="main-greeting">你好，幻话</h1>
              <p class="sub-greeting">开启智能对话新体验</p>
              <p class="welcome-desc">Welcome to the future of AI conversation</p>
            </div>
            
            <div class="action-section">
              <button class="primary-btn" @click="showAddDialog">
                <i class="el-icon-plus"></i>
                创建智能体
              </button>
              <button class="secondary-btn" @click="goToRoleConfig">
                <i class="el-icon-setting"></i>
                配置管理
              </button>
            </div>
            
            <div class="stats-section">
              <div class="stat-item">
                <span class="stat-number">{{ devices.length }}</span>
                <span class="stat-label">智能体</span>
              </div>
              <div class="stat-divider"></div>
              <div class="stat-item">
                <span class="stat-number">{{ devices.filter(d => d.deviceCount > 0).length }}</span>
                <span class="stat-label">在线设备</span>
              </div>
            </div>
          </div>
          
          <div class="hero-right">
            <div class="hero-visual">
              <div class="floating-card card-1">
                <div class="card-icon">🤖</div>
                <div class="card-text">AI 助手</div>
              </div>
              <div class="floating-card card-2">
                <div class="card-icon">💬</div>
                <div class="card-text">智能对话</div>
              </div>
              <div class="floating-card card-3">
                <div class="card-icon">⚡</div>
                <div class="card-text">实时响应</div>
              </div>
              <div class="hero-circle"></div>
            </div>
          </div>
        </div>
      </div>

      <!-- 智能体列表区域 -->
      <div class="agents-section">
        <div class="section-header">
          <h2 class="section-title">我的智能体</h2>
          <p class="section-subtitle">管理您的AI助手集合</p>
        </div>
        
        <div class="agents-grid">
          <template v-if="isLoading">
            <div v-for="i in skeletonCount" :key="'skeleton-' + i" class="skeleton-card">
              <div class="skeleton-header"></div>
              <div class="skeleton-content">
                <div class="skeleton-line"></div>
                <div class="skeleton-line-short"></div>
              </div>
            </div>
          </template>

          <template v-else>
            <DeviceItem v-for="(item, index) in devices" :key="index" :device="item" @configure="goToRoleConfig"
              @deviceManage="handleDeviceManage" @delete="handleDeleteAgent" @chat-history="handleShowChatHistory" />
          </template>
        </div>
      </div>
    </div>

    <AddWisdomBodyDialog :visible.sync="addDeviceDialogVisible" @confirm="handleWisdomBodyAdded" />
    <chat-history-dialog :visible.sync="showChatHistory" :agent-id="currentAgentId" :agent-name="currentAgentName" />
    
    <!-- 页脚 -->
    <footer class="app-footer">
      <version-footer />
    </footer>
  </div>
</template>

<script>
import Api from '@/apis/api';
import AddWisdomBodyDialog from '@/components/AddWisdomBodyDialog.vue';
import ChatHistoryDialog from '@/components/ChatHistoryDialog.vue';
import DeviceItem from '@/components/DeviceItem.vue';
import HeaderBar from '@/components/HeaderBar.vue';
import VersionFooter from '@/components/VersionFooter.vue';

export default {
  name: 'HomePage',
  components: { DeviceItem, AddWisdomBodyDialog, HeaderBar, VersionFooter, ChatHistoryDialog },
  data() {
    return {
      addDeviceDialogVisible: false,
      devices: [],
      originalDevices: [],
      isSearching: false,
      searchRegex: null,
      isLoading: true,
      skeletonCount: localStorage.getItem('skeletonCount') || 8,
      showChatHistory: false,
      currentAgentId: '',
      currentAgentName: ''
    }
  },

  mounted() {
    this.fetchAgentList();
  },

  methods: {
    showAddDialog() {
      this.addDeviceDialogVisible = true
    },
    goToRoleConfig() {
      // 点击配置角色后跳转到角色配置页
      this.$router.push('/role-config')
    },
    handleWisdomBodyAdded(res) {
      this.fetchAgentList();
      this.addDeviceDialogVisible = false;
    },
    handleDeviceManage() {
      this.$router.push('/device-management');
    },
    handleSearch(regex) {
      this.isSearching = true;
      this.searchRegex = regex;
      this.applySearchFilter();
    },
    handleSearchReset() {
      this.isSearching = false;
      this.searchRegex = null;
      this.devices = [...this.originalDevices];
    },
    applySearchFilter() {
      if (!this.isSearching || !this.searchRegex) {
        this.devices = [...this.originalDevices];
        return;
      }

      this.devices = this.originalDevices.filter(device => {
        return this.searchRegex.test(device.agentName);
      });
    },
    // 搜索更新智能体列表
    handleSearchResult(filteredList) {
      this.devices = filteredList; // 更新设备列表
    },
    // 获取智能体列表
    fetchAgentList() {
      this.isLoading = true;
      Api.agent.getAgentList(({ data }) => {
        if (data?.data) {
          this.originalDevices = data.data.map(item => ({
            ...item,
            agentId: item.id
          }));

          // 动态设置骨架屏数量（可选）
          this.skeletonCount = Math.min(
            Math.max(this.originalDevices.length, 3), // 最少3个
            10 // 最多10个
          );

          this.handleSearchReset();
        }
        this.isLoading = false;
      }, (error) => {
        console.error('Failed to fetch agent list:', error);
        this.isLoading = false;
      });
    },
    // 删除智能体
    handleDeleteAgent(agentId) {
      this.$confirm('确定要删除该智能体吗？', '提示', {
        confirmButtonText: '确定',
        cancelButtonText: '取消',
        type: 'warning'
      }).then(() => {
        Api.agent.deleteAgent(agentId, (res) => {
          if (res.data.code === 0) {
            this.$message.success({
              message: '删除成功',
              showClose: true
            });
            this.fetchAgentList(); // 刷新列表
          } else {
            this.$message.error({
              message: res.data.msg || '删除失败',
              showClose: true
            });
          }
        });
      }).catch(() => { });
    },
    handleShowChatHistory({ agentId, agentName }) {
      this.currentAgentId = agentId;
      this.currentAgentName = agentName;
      this.showChatHistory = true;
    }
  }
}
</script>

<style scoped>
/* 全局样式 */
.welcome {
  min-height: 100vh;
  background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
  position: relative;
  overflow-x: hidden;
}

.welcome::before {
  content: '';
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: 
    radial-gradient(circle at 20% 50%, rgba(120, 119, 198, 0.3) 0%, transparent 50%),
    radial-gradient(circle at 80% 20%, rgba(255, 119, 198, 0.15) 0%, transparent 50%),
    radial-gradient(circle at 40% 80%, rgba(120, 199, 255, 0.2) 0%, transparent 50%);
  pointer-events: none;
}

/* 主要内容区 */
.main-content {
  position: relative;
  z-index: 1;
  min-height: calc(100vh - 140px);
}

/* 英雄横幅区域 */
.hero-banner {
  padding: 40px 20px 60px;
  color: white;
}

.hero-content {
  max-width: 1200px;
  margin: 0 auto;
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 60px;
  align-items: center;
  min-height: 400px;
}

.hero-left {
  display: flex;
  flex-direction: column;
  gap: 30px;
}

.greeting-section {
  text-align: left;
}

.main-greeting {
  font-size: 3.5rem;
  font-weight: 800;
  margin: 0 0 10px 0;
  background: linear-gradient(135deg, #ffffff 0%, #f0f8ff 100%);
  -webkit-background-clip: text;
  -webkit-text-fill-color: transparent;
  background-clip: text;
  text-shadow: 0 4px 20px rgba(255, 255, 255, 0.3);
}

.sub-greeting {
  font-size: 1.3rem;
  margin: 0 0 8px 0;
  color: rgba(255, 255, 255, 0.9);
  font-weight: 500;
}

.welcome-desc {
  font-size: 1rem;
  margin: 0;
  color: rgba(255, 255, 255, 0.7);
  font-style: italic;
}

/* 操作按钮区域 */
.action-section {
  display: flex;
  gap: 16px;
  flex-wrap: wrap;
}

.primary-btn, .secondary-btn {
  padding: 12px 24px;
  border-radius: 50px;
  font-size: 16px;
  font-weight: 600;
  border: none;
  cursor: pointer;
  transition: all 0.3s ease;
  display: flex;
  align-items: center;
  gap: 8px;
  min-width: 140px;
  justify-content: center;
}

.primary-btn {
  background: linear-gradient(135deg, #ff6b6b 0%, #ee5a24 100%);
  color: white;
  box-shadow: 0 8px 25px rgba(255, 107, 107, 0.4);
}

.primary-btn:hover {
  transform: translateY(-2px);
  box-shadow: 0 12px 35px rgba(255, 107, 107, 0.6);
}

.secondary-btn {
  background: rgba(255, 255, 255, 0.15);
  color: white;
  border: 2px solid rgba(255, 255, 255, 0.3);
  backdrop-filter: blur(10px);
}

.secondary-btn:hover {
  background: rgba(255, 255, 255, 0.25);
  border-color: rgba(255, 255, 255, 0.5);
  transform: translateY(-2px);
}

/* 统计信息区域 */
.stats-section {
  display: flex;
  align-items: center;
  gap: 20px;
  padding: 20px 0;
}

.stat-item {
  display: flex;
  flex-direction: column;
  align-items: center;
  text-align: center;
}

.stat-number {
  font-size: 2rem;
  font-weight: 700;
  color: #fff;
  line-height: 1;
}

.stat-label {
  font-size: 0.9rem;
  color: rgba(255, 255, 255, 0.8);
  margin-top: 4px;
}

.stat-divider {
  width: 1px;
  height: 40px;
  background: rgba(255, 255, 255, 0.3);
}

/* 右侧视觉区域 */
.hero-right {
  display: flex;
  justify-content: center;
  align-items: center;
}

.hero-visual {
  position: relative;
  width: 300px;
  height: 300px;
}

.hero-circle {
  position: absolute;
  top: 50%;
  left: 50%;
  width: 200px;
  height: 200px;
  border-radius: 50%;
  background: linear-gradient(135deg, rgba(255, 255, 255, 0.1) 0%, rgba(255, 255, 255, 0.05) 100%);
  backdrop-filter: blur(20px);
  border: 1px solid rgba(255, 255, 255, 0.2);
  transform: translate(-50%, -50%);
  animation: pulse 4s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { transform: translate(-50%, -50%) scale(1); }
  50% { transform: translate(-50%, -50%) scale(1.05); }
}

.floating-card {
  position: absolute;
  background: rgba(255, 255, 255, 0.15);
  backdrop-filter: blur(20px);
  border: 1px solid rgba(255, 255, 255, 0.2);
  border-radius: 16px;
  padding: 16px;
  color: white;
  text-align: center;
  animation: float 6s ease-in-out infinite;
}

.card-1 {
  top: 20px;
  right: 20px;
  animation-delay: 0s;
}

.card-2 {
  bottom: 60px;
  left: 20px;
  animation-delay: 2s;
}

.card-3 {
  top: 60px;
  left: 50%;
  transform: translateX(-50%);
  animation-delay: 4s;
}

@keyframes float {
  0%, 100% { transform: translateY(0px); }
  50% { transform: translateY(-10px); }
}

.card-icon {
  font-size: 24px;
  margin-bottom: 8px;
}

.card-text {
  font-size: 12px;
  font-weight: 500;
}

/* 智能体列表区域 */
.agents-section {
  background: rgba(255, 255, 255, 0.95);
  backdrop-filter: blur(20px);
  margin: 0 20px;
  border-radius: 20px 20px 0 0;
  padding: 40px;
  min-height: 400px;
}

.section-header {
  text-align: center;
  margin-bottom: 40px;
}

.section-title {
  font-size: 2.2rem;
  font-weight: 700;
  color: #2d3748;
  margin: 0 0 8px 0;
}

.section-subtitle {
  font-size: 1.1rem;
  color: #718096;
  margin: 0;
}

.agents-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(350px, 1fr));
  gap: 24px;
}

/* 骨架屏样式 */
.skeleton-card {
  background: white;
  border-radius: 16px;
  padding: 24px;
  height: 140px;
  position: relative;
  overflow: hidden;
  border: 1px solid #e2e8f0;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.05);
}

.skeleton-header {
  width: 100%;
  height: 24px;
  background: #f7fafc;
  border-radius: 8px;
  margin-bottom: 16px;
}

.skeleton-content {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.skeleton-line {
  height: 16px;
  background: #f7fafc;
  border-radius: 8px;
  width: 70%;
}

.skeleton-line-short {
  height: 12px;
  background: #f7fafc;
  border-radius: 6px;
  width: 50%;
}

@keyframes shimmer {
  0% { transform: translateX(-100%); }
  100% { transform: translateX(100%); }
}

.skeleton-card::after {
  content: '';
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: linear-gradient(90deg,
    transparent,
    rgba(255, 255, 255, 0.6),
    transparent
  );
  animation: shimmer 2s infinite;
}

/* 页脚 */
.app-footer {
  background: rgba(255, 255, 255, 0.1);
  backdrop-filter: blur(20px);
  color: rgba(255, 255, 255, 0.8);
  text-align: center;
  padding: 20px;
  margin-top: auto;
}

/* 响应式设计 */
@media (max-width: 768px) {
  .hero-content {
    grid-template-columns: 1fr;
    gap: 40px;
    text-align: center;
  }
  
  .main-greeting {
    font-size: 2.5rem;
  }
  
  .action-section {
    justify-content: center;
  }
  
  .agents-grid {
    grid-template-columns: 1fr;
  }
  
  .hero-visual {
    width: 250px;
    height: 250px;
  }
}

@media (max-width: 480px) {
  .main-content {
    margin: 0 10px;
  }
  
  .hero-banner {
    padding: 20px 10px 40px;
  }
  
  .main-greeting {
    font-size: 2rem;
  }
}
</style>