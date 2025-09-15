import json
import asyncio
import time
from core.providers.tts.dto.dto import SentenceType
from core.utils import textUtils
from config.logger import setup_logging

TAG = __name__
logger = setup_logging()


async def sendAudioMessage(conn, sentenceType, audios, text):
    # 过滤空音频数据，避免播放中断
    if audios is None or len(audios) == 0:
        conn.logger.bind(tag=TAG).warning(f"跳过空音频数据: {sentenceType}, {text}")
        return
    
    # 发送句子开始消息
    conn.logger.bind(tag=TAG).info(f"发送音频消息: {sentenceType}, {text}, 音频帧数: {len(audios)}")

    pre_buffer = False
    if conn.tts.tts_audio_first_sentence:
        conn.logger.bind(tag=TAG).info(f"发送第一段语音: {text}")
        conn.tts.tts_audio_first_sentence = False
        pre_buffer = True

    await send_tts_message(conn, "sentence_start", text)

    await sendAudio(conn, audios, pre_buffer)

    await send_tts_message(conn, "sentence_end", text)

    # 发送结束消息（如果是最后一个文本）
    if conn.llm_finish_task and sentenceType == SentenceType.LAST:
        await send_tts_message(conn, "stop", None)
        conn.client_is_speaking = False
        if conn.close_after_chat:
            await conn.close()


# 播放音频
async def sendAudio(conn, audios, pre_buffer=True):
    if audios is None or len(audios) == 0:
        return
    
    # 检测是否为硬件设备（基于User-Agent或其他标识）
    is_hardware_device = _is_hardware_device(conn)
    
    if is_hardware_device:
        logger.bind(tag=TAG).info(f"使用硬件设备优化策略，音频帧数: {len(audios)}")
        await _sendAudio_hardware_optimized(conn, audios, pre_buffer)
    else:
        logger.bind(tag=TAG).info(f"使用网页端优化策略，音频帧数: {len(audios)}")
        await _sendAudio_web_optimized(conn, audios, pre_buffer)


async def _sendAudio_hardware_optimized(conn, audios, pre_buffer=True):
    """针对硬件设备优化的音频发送策略"""
    
    # 硬件设备参数优化
    frame_duration = 60  # 帧时长（毫秒）
    
    if pre_buffer:
        # 🔥 平滑预缓冲策略：保持语调一致性
        pre_buffer_frames = min(6, len(audios))  # 360ms预缓冲，减少预缓冲帧数
        conn.logger.bind(tag=TAG).info(f"硬件设备预缓冲: {pre_buffer_frames} 帧 (360ms)")
        
        # 🎵 关键优化：渐进式间隔，确保语调平滑过渡
        for i in range(pre_buffer_frames):
            if conn.client_abort:
                break
            await conn.websocket.send(audios[i])
            
            if i < pre_buffer_frames - 1:
                # 渐进式间隔：从快到标准，保持语调一致
                if i < 2:  # 前2帧稍快，解决开头卡顿
                    await asyncio.sleep(0.045)  # 45ms
                else:  # 后续帧使用标准间隔
                    await asyncio.sleep(0.055)  # 55ms，接近标准60ms
        
        remaining_audios = audios[pre_buffer_frames:]
    else:
        remaining_audios = audios
    
    # 发送剩余音频 - 标准间隔，保持语调稳定
    for i, opus_packet in enumerate(remaining_audios):
        if conn.client_abort:
            break
            
        conn.last_activity_time = time.time() * 1000
        await conn.websocket.send(opus_packet)
        
        # 使用标准间隔，保持语调自然
        if i < len(remaining_audios) - 1:  # 最后一帧不需要延迟
            await asyncio.sleep(0.058)  # 58ms间隔，接近标准60ms但稍微流畅


async def _sendAudio_web_optimized(conn, audios, pre_buffer=True):
    """针对网页端优化的音频发送策略（原有逻辑）"""
    # 流控参数优化
    frame_duration = 60  # 帧时长（毫秒），匹配 Opus 编码
    frame_duration_sec = frame_duration / 1000.0
    start_time = time.perf_counter()
    play_position = 0
    
    # 网络抖动容忍度和累积误差控制
    jitter_tolerance = 0.005  # 5ms 抖动容忍
    max_cumulative_drift = 0.020  # 最大累积误差 20ms

    # 仅当第一句话时执行预缓冲
    if pre_buffer:
        pre_buffer_frames = min(5, len(audios))  # 300ms预缓冲
        
        for i in range(pre_buffer_frames):
            if conn.client_abort:
                break
            
            if i > 0:  # 第一帧立即发送
                await asyncio.sleep(0.003)  # 3ms间隔
            
            await conn.websocket.send(audios[i])
            play_position += frame_duration
            
        remaining_audios = audios[pre_buffer_frames:]
    else:
        remaining_audios = audios

    # 播放剩余音频帧 - 精确时间控制
    for opus_packet in remaining_audios:
        if conn.client_abort:
            break

        conn.last_activity_time = time.time() * 1000

        # 计算预期发送时间
        expected_time = start_time + (play_position / 1000)
        current_time = time.perf_counter()
        delay = expected_time - current_time
        
        # 精细化延迟控制
        if delay > jitter_tolerance:
            max_delay = min(frame_duration_sec * 0.8, max_cumulative_drift)
            actual_delay = min(delay, max_delay)
            await asyncio.sleep(actual_delay)
        elif delay < -max_cumulative_drift:
            conn.logger.bind(tag=TAG).warning(f"音频发送延迟过大: {delay*1000:.1f}ms，跳过延迟")

        await conn.websocket.send(opus_packet)
        play_position += frame_duration


def _is_hardware_device(conn):
    """检测是否为硬件设备"""
    try:
        # 检查User-Agent或其他设备标识
        user_agent = getattr(conn, 'headers', {}).get('user-agent', '').lower()
        device_id = getattr(conn, 'device_id', '')
        logger.bind(tag=TAG).info(f"User-Agent: {user_agent}, Device-ID: {device_id}")
        
        # 判断是否为Web设备（仅当User-Agent包含特定浏览器标识时）
        web_indicators = ['mozilla', 'chrome', 'safari', 'firefox', 'edg', 'webkit']
        is_web = any(indicator in user_agent for indicator in web_indicators)
        
        # 如果是Web设备，返回False，否则视为硬件设备
        return not is_web
        
    except Exception:
        return True  # 默认按硬件设备处理，更安全


async def send_tts_message(conn, state, text=None):
    """发送 TTS 状态消息"""
    message = {"type": "tts", "state": state, "session_id": conn.session_id}
    if text is not None:
        message["text"] = textUtils.check_emoji(text)

    # TTS播放结束
    if state == "stop":
        # 播放提示音
        tts_notify = conn.config.get("enable_stop_tts_notify", False)
        if tts_notify:
            stop_tts_notify_voice = conn.config.get(
                "stop_tts_notify_voice", "config/assets/tts_notify.mp3"
            )
            audios, _ = conn.tts.audio_to_opus_data(stop_tts_notify_voice)
            await sendAudio(conn, audios)
        # 清除服务端讲话状态
        conn.clearSpeakStatus()

    # 发送消息到客户端
    await conn.websocket.send(json.dumps(message))


async def send_stt_message(conn, text):
    end_prompt_str = conn.config.get("end_prompt", {}).get("prompt")
    if end_prompt_str and end_prompt_str == text:
        await send_tts_message(conn, "start")
        return

    """发送 STT 状态消息"""
    
    # 解析JSON格式，提取实际的用户说话内容
    display_text = text
    try:
        # 尝试解析JSON格式
        if text.strip().startswith('{') and text.strip().endswith('}'):
            parsed_data = json.loads(text)
            if isinstance(parsed_data, dict) and "content" in parsed_data:
                # 如果是包含说话人信息的JSON格式，只显示content部分
                display_text = parsed_data["content"]
                # 保存说话人信息到conn对象
                if "speaker" in parsed_data:
                    conn.current_speaker = parsed_data["speaker"]
    except (json.JSONDecodeError, TypeError):
        # 如果不是JSON格式，直接使用原始文本
        display_text = text
    stt_text = textUtils.get_string_no_punctuation_or_emoji(display_text)
    await conn.websocket.send(
        json.dumps({"type": "stt", "text": stt_text, "session_id": conn.session_id})
    )
    conn.client_is_speaking = True
    await send_tts_message(conn, "start")
