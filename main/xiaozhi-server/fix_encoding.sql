DELETE FROM ai_model_provider WHERE id='SYSTEM_TTS_AliyunDashScopeTTS';
DELETE FROM ai_model_config WHERE id='TTS_AliyunDashScopeTTS';
DELETE FROM ai_tts_voice WHERE tts_model_id='TTS_AliyunDashScopeTTS';

INSERT INTO ai_model_provider (id, model_type, provider_code, name, fields, sort, creator, create_date, updater, update_date) VALUES
('SYSTEM_TTS_AliyunDashScopeTTS', 'TTS', 'aliyun_dashscope', 'AliyunDashScope TTS', '[{"key":"api_key","label":"API Key","type":"string"},{"key":"model","label":"Model","type":"string"},{"key":"format","label":"Format","type":"string"},{"key":"sample_rate","label":"Sample Rate","type":"string"},{"key":"voice","label":"Voice","type":"string"}]', 15, 1, NOW(), 1, NOW());

INSERT INTO ai_model_config VALUES ('TTS_AliyunDashScopeTTS', 'TTS', 'AliyunDashScopeTTS', 'AliyunDashScope TTS', 0, 1, '{"type": "aliyun_dashscope", "api_key": "your_api_key", "model": "sambert-zhiying-v1", "format": "wav", "sample_rate": "48000", "output_dir": "tmp/"}', NULL, NULL, 18, NULL, NULL, NULL, NULL);

INSERT INTO ai_tts_voice VALUES 
('TTS_AliyunDashScopeTTS_0001', 'TTS_AliyunDashScopeTTS', 'zhiying', 'sambert-zhiying-v1', 'Chinese', NULL, NULL, 1, NULL, NULL, NULL, NULL),
('TTS_AliyunDashScopeTTS_0002', 'TTS_AliyunDashScopeTTS', 'zhicheng', 'sambert-zhicheng-v1', 'Chinese', NULL, NULL, 2, NULL, NULL, NULL, NULL),
('TTS_AliyunDashScopeTTS_0003', 'TTS_AliyunDashScopeTTS', 'zhiwei', 'sambert-zhiwei-v1', 'Chinese', NULL, NULL, 3, NULL, NULL, NULL, NULL),
('TTS_AliyunDashScopeTTS_0004', 'TTS_AliyunDashScopeTTS', 'zhiqian', 'sambert-zhiqian-v1', 'Chinese', NULL, NULL, 4, NULL, NULL, NULL, NULL),
('TTS_AliyunDashScopeTTS_0005', 'TTS_AliyunDashScopeTTS', 'zhichen', 'sambert-zhichen-v1', 'Chinese', NULL, NULL, 5, NULL, NULL, NULL, NULL); 