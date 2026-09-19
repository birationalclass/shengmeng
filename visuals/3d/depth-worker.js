// Inference stays in a worker so model loading and WASM cannot block the UI.
import {normalizeDepth} from './geometry.js?v=20260919-2';
let estimator;
let backend;
let busy = false;
const MODEL = 'onnx-community/depth-anything-v2-small';
const REVISION = '4472b7362082ad9968fee890ca0f1e5aca36b93d';
self.onmessage = async ({ data }) => {
  if (busy) return;
  busy = true;
  const { id, image } = data;
  const report = (type, payload = {}) => self.postMessage({ id, type, ...payload });
  try {
    report('status', { message: '正在加载 AI 引擎…' });
    const { pipeline, env } = await import('./vendor/transformers.min.js');
    env.allowLocalModels = false;
    env.backends.onnx.wasm.numThreads = 1;
    const progress_callback = (event) => {
      if (event.status === 'progress') report('progress', {
        progress: event.progress,
        message: `下载模型 ${Math.round((event.loaded || 0) / 1048576)} / ${Math.round((event.total || 0) / 1048576)} MB`
      });
    };
    if (!estimator) {
      let adapter;
      try { adapter = await navigator.gpu?.requestAdapter(); } catch { /* WASM below */ }
      if (adapter) {
        backend = 'WebGPU';
        try {
          estimator = await pipeline('depth-estimation', MODEL, { revision: REVISION, device: 'webgpu', dtype: 'fp32', progress_callback });
        } catch {
          report('status', { message: 'GPU 不支持此模型，正在切换兼容模式…' });
        }
      }
      if (!estimator) {
        backend = 'WASM';
        estimator = await pipeline('depth-estimation', MODEL, { revision: REVISION, device: 'wasm', dtype: 'q8', progress_callback });
      }
    }
    report('infer', { message: `正在估计深度 · ${backend}（首次运行可能需要片刻）` });
    let result;
    try { result = await estimator(image); }
    catch (error) {
      if (backend !== 'WebGPU') throw error;
      await estimator.dispose().catch(() => {});
      estimator = null;
      backend = 'WASM';
      report('status', { message: 'GPU 推理未完成，切换兼容模式…' });
      estimator = await pipeline('depth-estimation', MODEL, { revision: REVISION, device: 'wasm', dtype: 'q8', progress_callback });
      report('infer', { message: '正在估计深度 · WASM' });
      result = await estimator(image);
    }
    const { depth, predicted_depth } = result;
    // Preserve floating-point prediction; the display PNG is only 8-bit.
    const values = normalizeDepth(predicted_depth.data);
    if(values.length!==depth.width*depth.height) throw new Error('Unexpected depth dimensions');
    self.postMessage({ id, type: 'result', values, width: depth.width, height: depth.height, backend }, [values.buffer]);
  } catch (error) {
    estimator = null;
    report('error', { message: String(error?.message || error) });
  } finally { busy = false; }
};
