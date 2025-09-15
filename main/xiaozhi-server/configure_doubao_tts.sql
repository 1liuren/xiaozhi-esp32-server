-- 配置豆包语音合成大模型
-- 请将下面的 "你的appid" 和 "你的access_token" 替换为你在火山引擎控制台获取的实际值

UPDATE ai_model_config 
SET config_json = JSON_OBJECT(
  'type', 'huoshan_double_stream',
  'appid', '8382474478',
  'ws_url', 'wss://openspeech.bytedance.com/api/v3/tts/bidirection',
  'speaker', 'zh_female_wanwanxiaohe_moon_bigtts',
  'resource_id', 'volc.service_type.10029',
  'access_token', 'h3hA0GIgoegUHHNp3_1iR2zYPiljmZMe'
),
is_enabled = 1,
update_date = NOW()
WHERE id = 'TTS_HuoshanDoubleStreamTTS';

-- 查看更新结果
SELECT id, model_name, is_enabled, config_json 
FROM ai_model_config 
WHERE id = 'TTS_HuoshanDoubleStreamTTS';
