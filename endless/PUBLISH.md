# 发布到 GitHub 个人主页

## 当前状态

- 已把运行文件接入 `sheng-meng-homepage/endless/`；
- 已在主页 AI4Games 区增加《无尽》项目卡片，并把首页试玩按钮指向 `/endless/`；
- 已保留旧 `/game/` 项目；
- 已创建本地提交 `3c1e92e Add Endless card-combo defense game`；
- 本机分支当前比 `origin/main` 超前 1 个提交；
- 账号与可恢复存档功能已完成浏览器验收，并已同步到 `sheng-meng-homepage/endless/`；
- GitHub 网页端已经登录，命令行推送凭据仍需完成连接。

登录 GitHub 后只需在 `sheng-meng-homepage` 目录运行 `git push origin main`，随后现有 GitHub Actions 会自动部署。

现有个人主页仓库：

- 本地目录：`sheng-meng-homepage`
- 远端：`https://github.com/birationalclass/shengmeng.git`
- 分支：`main`
- 在线地址：`https://birationalclass.github.io/shengmeng/`
- 发布方式：`.github/workflows/pages.yml` 在 `main` 分支推送后自动部署整个静态目录。

## 推荐接入方式

保留旧游戏的 `/game/` 地址，把《无尽》独立放在 `/endless/`：

```text
sheng-meng-homepage/
├─ game/            # 旧游戏，保持不变
├─ endless/         # 《无尽》
│  ├─ index.html
│  ├─ styles.css
│  └─ game.js
├─ index.html       # 增加《无尽》项目卡片
├─ .nojekyll
└─ .github/workflows/pages.yml
```

完成本地验收后：

1. 将《无尽》的三个运行文件同步到 `sheng-meng-homepage/endless/`；
2. 在主页 `AI4Games` 区域增加《无尽》项目卡片，链接写为 `endless/`；
3. 在主页目录启动静态服务器并验证 `/`、`/game/`、`/endless/`；
4. 检查 `git diff`，只提交新游戏和对应主页入口；
5. 推送 `main` 后等待 GitHub Actions 的 Pages 工作流成功；
6. 最终验证 `https://birationalclass.github.io/shengmeng/endless/`。

建议提交信息：

```text
Add Endless card-combo defense game
```

发布前不要删除旧游戏，也不要复用旧游戏的本地存档键。《无尽》使用独立的 `endless-defense-accounts-v1`，其中按本机账号隔离最佳纪录和进行中存档。
