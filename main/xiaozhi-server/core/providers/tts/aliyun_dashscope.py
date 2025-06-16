import dashscope
from dashscope.audio.tts import SpeechSynthesizer
from core.providers.tts.base import TTSProviderBase
from core.utils.util import check_model_key
from config.logger import setup_logging
import sys

TAG = __name__
logger = setup_logging()


class TTSProvider(TTSProviderBase):
    def __init__(self, config, delete_audio_file):
        super().__init__(config, delete_audio_file)
        
        # 从配置获取API Key
        self.api_key = config.get("api_key")
        check_model_key("阿里DashScope TTS", self.api_key)
        
        # 设置API Key到dashscope
        dashscope.api_key = self.api_key
        
        # 从配置获取模型名称
        self.model = config.get("model", "sambert-zhiying-v1")
        
        # 从配置获取音频格式和采样率
        self.format = config.get("format", "wav")
        self.audio_file_type = config.get("format", "wav")
        
        # 处理采样率配置
        sample_rate = config.get("sample_rate", "48000")
        self.sample_rate = int(sample_rate) if sample_rate else 48000
        
        # 支持自定义音色
        if config.get("private_voice"):
            self.voice = config.get("private_voice")
        else:
            self.voice = config.get("voice", None)
        
        logger.bind(tag=TAG).info(f"初始化阿里DashScope TTS - 模型: {self.model}, 采样率: {self.sample_rate}, 格式: {self.format}")

    async def text_to_speak(self, text, output_file):
        """
        将文本转换为语音
        
        Args:
            text: 要转换的文本
            output_file: 输出文件路径，如果为None则返回音频二进制数据
            
        Returns:
            如果output_file为None，返回音频二进制数据；否则返回输出文件路径
        """
        try:
            # 根据DashScope官方文档构建调用参数
            call_params = {
                'model': self.model,
                'text': text,
                'sample_rate': self.sample_rate,
                'format': self.format
            }
            
            logger.bind(tag=TAG).info(f"调用DashScope TTS - 参数: {call_params}")
            
            # 调用DashScope TTS服务
            result = SpeechSynthesizer.call(**call_params)
            
            logger.bind(tag=TAG).info(f"DashScope TTS响应: {result}")
            
            # 检查响应
            if result.get_audio_data() is not None:
                audio_data = result.get_audio_data()
                logger.bind(tag=TAG).info(f"成功获取音频数据，大小: {sys.getsizeof(audio_data)} 字节")
                
                # 处理输出
                if output_file:
                    # 保存到文件
                    with open(output_file, 'wb') as f:
                        f.write(audio_data)
                    logger.bind(tag=TAG).info(f"音频已保存到: {output_file}")
                    return output_file
                else:
                    # 返回音频二进制数据
                    return audio_data
            else:
                # 打印错误详情
                response = result.get_response()
                logger.bind(tag=TAG).error(f"DashScope TTS调用失败，响应: {response}")
                raise Exception(f"DashScope TTS调用失败：{response}")
                
        except Exception as e:
            error_msg = f"阿里DashScope TTS请求失败: {str(e)}"
            logger.bind(tag=TAG).error(error_msg)
            raise Exception(error_msg) 