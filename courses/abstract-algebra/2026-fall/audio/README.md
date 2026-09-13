# 甘道夫台词原声 · 山谷回声版

- 来源：用户指定的 [B 站铭文片段](https://www.bilibili.com/video/BV1xL4y1u7xZ/)。取公开音轨约 21.66–33.70 秒的四句台词。
- 使用 [audio-separator](https://github.com/nomadkaraoke/python-audio-separator) 0.47.0 和 Kimberley Jensen 的 `vocals_mel_band_roformer.ckpt` 分离人声；先处理包含前后文的音频，再裁出 12.04 秒台词。保留实际演员录音，没有合成配音。
- 对分离人声做 65 Hz 高通、8.5 kHz 低通；左右声道加入 270–2510 ms 的错开反射，叠加约 3.2 秒衰减的扩散混响。保留中央直达人声，追加 4.4 秒尾音，末尾自然淡出。
- 成品 `gandalf-ring-verse-valley.mp3`：48 kHz，双声道，192 kbps，约 16.44 秒（含尾音）。FFmpeg 响度目标 −16 LUFS、真峰值上限 −1.5 dBTP；编码后实测 −17.34 LUFS、−1.70 dBTP。
- 环场景台词出现时自动播放；播放和尾音期间暂停图案时间轴，结束后继续。人声音量设为 80%，不在画面显示原声按钮；原有页面背景音乐维持原音量，不再因台词播放而压低。

## 重制

`render-valley.py` 接收已分离、裁剪好的干声 WAV 和输出 WAV 路径，依赖 NumPy、SciPy、SoundFile。分离模型和中间素材不随网站发布。

```sh
python render-valley.py isolated-dialogue.wav valley-render.wav
ffmpeg -i valley-render.wav -af 'loudnorm=I=-16:TP=-1.5:LRA=9' -ar 48000 -c:a libmp3lame -b:a 192k -map_metadata -1 gandalf-ring-verse-valley.mp3
```

人声分离会抑制原片配乐和环境声；极轻的耳语仍受原始混音影响。
