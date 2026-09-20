# 佛香阁 · Real3D 视觉习作

参考用户指定的 [B 站视频](https://www.bilibili.com/video/BV1w2Y46aEAb/)，转载自 [Sac 的原帖](https://x.com/Saccc_c/status/2097225315089256814)。原帖说明采用 GPT 6 Astra + Blender，未公开工程或具体步骤；本作品是独立参数化重建，并非原模型，未经测绘核验。

屋顶、瓦垄、斗拱、栏杆、窗棂、阶梯、石台基和地形为程序生成的真实网格。树林使用 [Poly Haven island_tree_01](https://polyhaven.com/a/island_tree_01)，CC0，简化后复用。未使用视频截图贴在模型上，未使用 AI 修图。

静态图：Blender Cycles。交互版：Three.js + GLB，扫描纹理缩减至 1024px，实时光照与路径追踪效果不同。可拖动旋转、缩放、切换视角、显示线框，使用触屏或键盘操作。树木并非当地树种的准确复刻。

建模源代码见 [build.py](build.py)，需 Blender 4.5 及 Poly Haven 树木资产，修改路径后可重新生成。
