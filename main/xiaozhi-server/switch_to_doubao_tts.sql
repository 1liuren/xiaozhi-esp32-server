-- 将设备切换到豆包语音合成大模型
-- 将所有设备的TTS模型切换为豆包TTS

UPDATE ai_agent 
SET tts_model_id = 'TTS_HuoshanDoubleStreamTTS',
    updated_at = NOW()
WHERE tts_model_id IS NOT NULL;

-- 查看更新结果
SELECT agent_code, tts_model_id 
FROM ai_agent 
WHERE tts_model_id = 'TTS_HuoshanDoubleStreamTTS';
