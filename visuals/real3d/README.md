# Real3D / 水庭

可交互的真实三维庭院。拖动旋转，滚轮缩放，右键或双指平移。方向键旋转，+/- 缩放，0 复位。提供池畔、露台、全景与背面视角、全屏、线框、画质设置和静态精修图对照。

## 场景与渲染

场景来自同一个 Blender 参数化建筑模型。GLB 对远景植被进行了简化，采用 Draco 几何压缩；网页使用 Three.js 0.180.0 与现有 Spatial Studio 共用核心组件。所有模型、解码器、脚本和图像均随站点托管，无外部 CDN 运行依赖。实时玻璃、水面与程序化材质经过适配，不等同于 Blender 离线路径追踪渲染。

## 免费 CC0 素材

来自 [Poly Haven](https://polyhaven.com/license)：

- [Island Tree 01](https://polyhaven.com/a/island_tree_01)
- [Shrub 04](https://polyhaven.com/a/shrub_04)
- [Potted Plant 02](https://polyhaven.com/a/potted_plant_02)
- [Potted Plant 04](https://polyhaven.com/a/potted_plant_04)
- [Namaqualand Boulder 03](https://polyhaven.com/a/namaqualand_boulder_03)
- [Stone Wall 05](https://polyhaven.com/a/stone_wall_05)

Three.js components: MIT license, https://github.com/mrdoob/three.js
Draco decoder: Apache-2.0 license, https://github.com/google/draco
