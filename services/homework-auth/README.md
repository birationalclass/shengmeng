# 阅见：邮箱注册与私有作业系统

前端：`courses/homework/`。后端沿用群数独的腾讯 CloudBase 上海环境，但账号、会话、作业与设置使用独立集合，不共享群数独的弱身份会话。

## 身份与权限

- 学生以 11 位学号注册，验证码只发送到 `学号@stu.ecnu.edu.cn`。
- 教师输入 `smeng` 或 `smeng@math.ecnu.edu.cn`，验证码只发送到教师邮箱。客户端不能指定教师身份。
- 六位随机验证码，10 分钟有效，五次错误失效。发送冷却、频率限制与验证码消费使用数据库事务。密码使用随机盐和 scrypt；数据库只保留会话 token 的 SHA-256 摘要。
- 默认登录保留一天，可选择记住 30 天。跨域会话沿用群数独的 Bearer 方式，默认 sessionStorage，记住登录时 localStorage。密码不会保存在浏览器。找回密码会使全部旧会话失效。
- 所有作业列表、详情和扫描页都由服务器检查身份。教师可查看所有上传批次；学生只可查看 `published=true` 且学号为本人的作业。
- 发布必须由教师明确核对学号和页面归属。自动识别的学号不会直接授予学生访问权限。

## 上传、双版本与批改

PDF 由本地固定版本 PDF.js 渲染；图片和 PDF 页转成 JPEG，长边最多 1800 像素，每页最多 480 KB。每批最多 20 页、每个输入文件最多 30 MB。扫描版保留这些图像，电脑字体版按识别的段落忠实转录；不声称 AI 转录绝对准确。模糊字符明确标记，教师可校对。

为避免共享存储桶的公开权限影响隐私，扫描页存放于 ADMINONLY 的 `homework_pages` 集合，每页独立文档。图像只经逐次鉴权的 API 返回，不生成可公开读取的静态地址。原始 PDF 文件本身不上传，也不保留在服务器；扫描版是 PDF 的逐页图像。

使用 **OpenAI Responses API，`gpt-6-sol`，`reasoning.effort=medium`**：

1. 识别学生、页面归属和逐段原文，输出归一化坐标及稳定 block ID。
2. 对转录内容统一批改一次，不打分。两种视图引用同一批注数据，扫描版按坐标显示，电脑字体版按 block ID 显示。
3. 教师可修改批注；校正转录会撤回发布并清除旧批注，需重新批改。
4. 教师确认后发布，学生才可查看。

AI 使用 background + streaming。教师页面读取可恢复事件流，显示正在生成的结果、阶段和实际 token 用量；不显示私密思维链、不编造百分比或实时 token 数。每阶段完成后记录输入、缓存输入、输出和其中推理 token。页面关闭后当前模型请求继续；重新打开批次后恢复收集结果并推进下一阶段。`store=true` 用于跨页面恢复，数据也会发送至 OpenAI API 处理。

未设置 API key 时允许上传保存，启动 AI 返回明确的未配置错误。模型访问、余额或网络不可用时不返回伪造批改。首次正式使用前需以虚构作业检查实际模型表现、数学识别准确度和服务器至 OpenAI 的连通性。

## CloudBase 部署

- 环境：`birationalclass-d3fw2j6t76955af0`，地区 `ap-shanghai`。
- 函数：`homework-auth`，事件函数，Nodejs20.19，入口 `index.main`，256 MB，30 秒。
- HTTPS 路由：`/homework-auth`，与群数独一样通过 CreateCloudBaseGWAPI 映射事件函数。处理器自行检查来源与 Bearer 会话。
- 生产集合：`homework_users`、`homework_sessions`、`homework_challenges`、`homework_limits`、`homework_batches`、`homework_pages`、`homework_submissions`、`homework_settings`。全部必须设置 `ADMINONLY`。
- 测试集合采用 `homework_test_` 前缀，测试函数 `homework-auth-test`，只有虚构资料，不发送邮件或调用收费 AI。
- `sessions`、`challenges`、`limits` 的 `expiresOn` 字段建立 TTL 索引；代码也会独立检查过期，不能依赖 TTL 即时删除。
- `submissions` 建立 `{studentId:1,published:1,createdAt:-1}` 索引。

环境变量（通过私有配置提供，禁止写入 GitHub）：

| 变量 | 内容 |
|---|---|
| `AUTH_SECRET` | 至少 32 字符的持久随机密钥；同时用于验证码摘要和 AI 设置加密，不可随意轮换 |
| `AUTH_COLLECTION_PREFIX` | 生产为 `homework_` |
| `AUTH_ORIGINS` | `https://birationalclass.github.io`，只在测试时添加 localhost |
| `SMTP_USER` | `smeng@math.ecnu.edu.cn` |
| `SMTP_HOST` / `SMTP_PORT` | `smtphz.qiye.163.com` / `994`，TLS |
| `SMTP_PASSWORD` | 学校邮箱客户端授权密码，必须由邮箱所有者配置 |
| `OPENAI_API_KEY` | 作业系统专用密钥；也可在教师工作台「AI 设置」中输入 |

教师网页更新 API key 时需再次输入个人密码；服务器通过模型读取接口验证后，以 AES-256-GCM 加密保存至私有设置集合。密钥不会回显。环境变量密钥为回退值，教师设置优先。API key 至少需要 Responses 的读写和 Models 的读取权限，不需要管理组织、账单、文件或其他项目的权限。

## 验证与上线限制

运行 `node --test services/homework-auth/*.test.cjs`。测试覆盖注册验证、验证码并发消费、登录/重设/退出、会话过期、频率限制、教师权限、学生越权、扫描页保护、AI 状态转换、共享批注、发布、转录修改撤回，以及密钥加密。

实际发信必须在配置 SMTP 授权密码后验证，实际 AI 调用必须在专用 API key 及计费可用后验证。本地替身和云端虚构测试不能代替这两项真实验证。

官方参考：[学生邮箱](https://eoffice.ecnu.edu.cn/xsyx/list.htm)、[GPT-6 Sol](https://developers.openai.com/api/docs/models/gpt-6-sol)、[Responses 后台任务](https://developers.openai.com/api/docs/guides/background)、[结构化输出](https://developers.openai.com/api/docs/guides/structured-outputs)。
