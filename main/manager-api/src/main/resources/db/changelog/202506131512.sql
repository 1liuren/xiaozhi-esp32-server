-- 增加阿里DashScope TTS供应器和模型配置
delete from `ai_model_provider` where id = 'SYSTEM_TTS_AliyunDashScopeTTS';
INSERT INTO `ai_model_provider` (`id`, `model_type`, `provider_code`, `name`, `fields`, `sort`, `creator`, `create_date`, `updater`, `update_date`) VALUES
('SYSTEM_TTS_AliyunDashScopeTTS', 'TTS', 'aliyun_dashscope', '阿里DashScope语音合成', '[{"key":"api_key","label":"API密钥","type":"string"},{"key":"model","label":"模型名称","type":"string"},{"key":"format","label":"音频格式","type":"string"},{"key":"sample_rate","label":"采样率","type":"string"},{"key":"voice","label":"默认音色","type":"string"}]', 15, 1, NOW(), 1, NOW());

delete from `ai_model_config` where id = 'TTS_AliyunDashScopeTTS';
INSERT INTO `ai_model_config` VALUES ('TTS_AliyunDashScopeTTS', 'TTS', 'AliyunDashScopeTTS', '阿里DashScope语音合成', 0, 1, '{\"type\": \"aliyun_dashscope\", \"api_key\": \"你的阿里云DashScope_API_Key\", \"model\": \"sambert-zhiying-v1\", \"format\": \"wav\", \"sample_rate\": \"48000\", \"output_dir\": \"tmp/\"}', NULL, NULL, 18, NULL, NULL, NULL, NULL);

-- 阿里DashScope TTS模型配置说明文档
UPDATE `ai_model_config` SET 
`doc_link` = 'https://help.aliyun.com/zh/dashscope/developer-reference/speech-synthesis-quick-start',
`remark` = '阿里DashScope语音合成服务配置说明：
1. 申请地址：https://dashscope.aliyun.com/
2. API Key获取：https://dashscope.console.aliyun.com/apiKey
3. 支持多种高质量音色模型：
   - sambert-zhiying-v1: 知莺音色（中文女声）
   - sambert-zhicheng-v1: 知程音色（中文男声）
   - sambert-zhiwei-v1: 知微音色（中文女声，温和亲切）
   - sambert-zhiqian-v1: 知浅音色（中文女声，活泼可爱）
   - sambert-zhichen-v1: 知晨音色（中文男声，稳重大气）
4. 采样率支持：8000、16000、22050、24000、44100、48000
5. 音频格式支持：wav、mp3、pcm' WHERE `id` = 'TTS_AliyunDashScopeTTS';

-- 添加阿里DashScope TTS默认音色配置
delete from `ai_tts_voice` where tts_model_id = 'TTS_AliyunDashScopeTTS';
INSERT INTO `ai_tts_voice` VALUES ('TTS_AliyunDashScopeTTS_0001', 'TTS_AliyunDashScopeTTS', '知莺（女声）', 'sambert-zhiying-v1', '中文', NULL, NULL, 1, NULL, NULL, NULL, NULL);
INSERT INTO `ai_tts_voice` VALUES ('TTS_AliyunDashScopeTTS_0002', 'TTS_AliyunDashScopeTTS', '知程（男声）', 'sambert-zhicheng-v1', '中文', NULL, NULL, 2, NULL, NULL, NULL, NULL);
INSERT INTO `ai_tts_voice` VALUES ('TTS_AliyunDashScopeTTS_0003', 'TTS_AliyunDashScopeTTS', '知微（女声-温和）', 'sambert-zhiwei-v1', '中文', NULL, NULL, 3, NULL, NULL, NULL, NULL);
INSERT INTO `ai_tts_voice` VALUES ('TTS_AliyunDashScopeTTS_0004', 'TTS_AliyunDashScopeTTS', '知浅（女声-活泼）', 'sambert-zhiqian-v1', '中文', NULL, NULL, 4, NULL, NULL, NULL, NULL);
INSERT INTO `ai_tts_voice` VALUES ('TTS_AliyunDashScopeTTS_0005', 'TTS_AliyunDashScopeTTS', '知晨（男声-稳重）', 'sambert-zhichen-v1', '中文', NULL, NULL, 5, NULL, NULL, NULL, NULL); 