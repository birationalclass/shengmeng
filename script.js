const translations = {
  zh: {
    navResearch: "学术研究", navPubs: "论文", navVisuals: "可视化", navTools: "工具", navContact: "联系",
    heroKicker: "华东师范大学 · 研究员", heroLine1: "结构、动力，", heroLine2: "与智能发现。",
    heroIntro: "我研究代数几何与动力系统，并探索人工智能如何辅助数学推理、拓展战略世界与交互体验。", exploreResearch: "探索研究", playGame: "试玩《无尽》", openVisualLab: "可视化实验室", openPascal: "探索帕斯卡定理",
    coreFields: "2023 年以来的近期论文", phdYear: "新加坡国立大学数学博士", openQuestions: "开放问题，严谨方法", newFrontiers: "数学与游戏的新边界",
    researchTitle: "近期论文与预印本。", researchLead: "学术研究区只呈现论文本身，并将最新 arXiv 记录置于最前。", viewArxiv: "在 arXiv 查看作者检索结果",
    agTitle: "代数几何", agText: "射影簇、典范除子、环面结构与几何分类。", bgTitle: "双有理几何", bgText: "极小模型纲领、有理连通簇与结构分解。", dsTitle: "动力系统", dsText: "满射自同态、算术度、稠密轨道与动力刚性。",
    currentProgram: "当前研究计划", programText: "满射自同态的分类及其在算术动力系统中的应用，包括 Kawaguchi–Silverman 猜想与 Zariski 稠密轨道猜想。",
    exploratory: "探索方向", aiMathTitle: "让 AI 成为数学探索的伙伴。", aiMathLead: "研究机器智能如何辅助而非替代形式推理、猜想生成、文献导航与数学交流。",
    formalReasoning: "形式推理", formalText: "证明辅助、验证闭环与可解释的数学论证链。", conjectureDiscovery: "猜想发现", conjectureText: "通过计算实验发现值得证明的模式与值得理解的反例。", knowledgeSystems: "数学知识系统", knowledgeText: "结构化连接定义、定理、例子与依赖图谱。", msreaderText: "把 TeX 与 arXiv 论文整理成可交互的定理卡片、证明链接与可导航知识图谱的原生 macOS 阅读器。",
    msreaderNavOverview: "概览", msreaderNavWorkflow: "工作流", msreaderNavRequirements: "运行要求", msreaderNavHome: "返回主页", msreaderKicker: "原生 macOS 数学阅读工作台", msreaderLead: "把 TeX 与 arXiv 论文转化为可交互的定理卡片、证明链接，以及真正可以导航的数学知识图谱。", msreaderDownload: "下载 0.2 原型版", msreaderSeeWorkflow: "查看工作流", msreaderWorkflowTitle: "从论文到可导航的逻辑结构。", msreaderWorkflowLead: "保留原始数学内容，同时让论文的论证架构变得可见、可探索。", msreaderFeatureImport: "导入论文源文件", msreaderFeatureImportText: "打开 arXiv 页面或本地 TeX 文件，自动定位主文档并展开其中引用的源文件。", msreaderFeatureParse: "恢复逻辑关系", msreaderFeatureParseText: "在保留原始 TeX 的同时，将定理环境、编号、引用与证明关系转化为结构化数据。", msreaderFeatureExplore: "探索知识图谱", msreaderFeatureExploreText: "在玻璃质感的定理卡片间浏览，由 Metal 实时绘制当前论证的依赖路径。", msreaderReleaseTitle: "一款可以开始试用的原生阅读器。", msreaderReleaseLead: "0.2 版是面向 macOS 13 或更高版本的 Apple Silicon 原型，包含 arXiv 浏览器、本地 TeX 导入、定理卡片、MathJax 排版与 Metal 关系线。", msreaderDownloadZip: "下载 msreader 0.2", msreaderPlatform: "运行平台", msreaderVersion: "版本", msreaderArchive: "压缩包", msreaderSigningNote: "原型提示：此版本使用临时签名，尚未经过 Apple 公证。首次打开时，macOS 可能需要按住 Control 点击并选择“打开”。", msreaderFooter: "msreader · 让数学论文真正可以导航",
    visualBadge: "交互项目", visualTitle: "让数学结构在屏幕上运动。", visualLead: "从本地可视化项目转化而来的浏览器版实验：复动力系统、混沌流、直纹曲面与射影关联几何。", visualJuliaTitle: "Julia 集探索器", visualJuliaText: "缩放、平移，并跟随 WebGL 实时生成的复动力系统边界。", visualChaosTitle: "混沌吸引子画廊", visualChaosText: "把六个动力系统的轨道画成可旋转的发光流线。", visualBundleTitle: "直纹曲面的粘合", visualBundleText: "调节 Hirzebruch 指数，观察局部标架如何获得扭转。", visualPascalTitle: "帕斯卡六点共线", visualPascalText: "移动同一圆锥曲线上的六个点，观察三组对边交点始终落在同一直线上。", openVisual: "打开实验", enterVisualLab: "进入可视化实验室",
    creativeLab: "创意实验室", aiGamesTitle: "把游戏变成策略与智能的实验室。", aiGamesLead: "可玩系统让抽象规则变得可见。AI4Games 探索战略智能体、程序化世界，以及把数学结构转化为交互的游戏机制。",
    gameTitle: "疆域争锋", gameText: "从零构建的即时领地策略游戏：连通路径、多建筑指挥、进化式箭塔能力、自适应电脑军团与八张战役地图。", gameFeature1: "拖拽指挥与框选", gameFeature2: "五类建筑自由改建", gameFeature3: "本地账号与持久化战役进度", launchGame: "进入游戏",
    endlessTitle: "无尽", endlessText: "一款完全零付费的无尽防线游戏：塑造可靠牌池、发现跨元素循环，并用主动集火抵御持续增强的外星潮。", endlessFeature1: "六种决定流派的卡牌组合", endlessFeature2: "加权选牌与每波一次免费刷新", endlessFeature3: "主动集火与极限火力时机", launchEndless: "进入《无尽》",
    agentText: "在局部控制、资源压力与网络变化中的决策。", proceduralText: "生成有意义差异的规则，而非装饰性的随机。", learningText: "通过交互理解网络、动力系统与优化。",
    toolsTitle: "实用软件，即下即用。", toolsLead: "这里将持续收录专注、轻量的桌面工具与实验项目。", dlsgraphText: "最多五人使用的轻量级实时通信房间。其他电脑可直接查看待加入房间，点选后输入创建者告知的 4 位密码，无需复制长邀请。", dlsgraphFeature1: "短时有效的待加入房间大厅", dlsgraphFeature2: "4 位密码加入与 AES-256-GCM 加密", dlsgraphFeature3: "直连 / TURN 路径状态与实时 RTT", downloadWindows: "下载 Windows 版",
    publicationsTitle: "代表论文。", publicationsLead: "涵盖极化自同态、算术动力系统、双有理几何与紧复空间。", downloadCV: "下载简历", allPublications: "查看完整论文列表",
    journeyTitle: "学术经历。", ecnuRole: "数学科学学院教授 / 青年研究员", kiasRole: "研究员", mpiRole: "博士后研究员", nusRole: "数学博士 · 导师：张德祺",
    contactTitle: "一起探索一个困难问题。", contactLead: "欢迎就数学研究、学生培养以及数学、AI 与游戏的跨学科想法交流。", office: "办公室", institution: "单位", address: "地址", footerText: "数学 · 人工智能 · 游戏",
    brandName: "孟 晟"
  }
};

const defaultText = new Map();
document.querySelectorAll("[data-i18n]").forEach((node) => defaultText.set(node.dataset.i18n, node.textContent));

let language = "en";
const languageButton = document.querySelector("#languageButton");
languageButton.addEventListener("click", () => {
  language = language === "en" ? "zh" : "en";
  document.documentElement.lang = language === "zh" ? "zh-CN" : "en";
  document.querySelectorAll("[data-i18n]").forEach((node) => {
    node.textContent = language === "zh" ? translations.zh[node.dataset.i18n] || defaultText.get(node.dataset.i18n) : defaultText.get(node.dataset.i18n);
  });
  languageButton.textContent = language === "zh" ? "EN" : "中文";
});

const menuButton = document.querySelector("#menuButton");
const nav = document.querySelector("#mainNav");
menuButton.addEventListener("click", () => {
  const open = nav.classList.toggle("open");
  menuButton.setAttribute("aria-expanded", String(open));
});
nav.querySelectorAll("a").forEach((link) => link.addEventListener("click", () => {
  nav.classList.remove("open");
  menuButton.setAttribute("aria-expanded", "false");
}));

const revealObserver = new IntersectionObserver((entries) => entries.forEach((entry) => {
  if (entry.isIntersecting) {
    entry.target.classList.add("visible");
    revealObserver.unobserve(entry.target);
  }
}), { threshold: 0.12 });
document.querySelectorAll(".reveal").forEach((node) => revealObserver.observe(node));

const sections = [...document.querySelectorAll("main section[id]")];
const navLinks = [...nav.querySelectorAll("a[href^='#']")];
const sectionObserver = new IntersectionObserver((entries) => entries.forEach((entry) => {
  if (entry.isIntersecting) {
    navLinks.forEach((link) => link.classList.toggle("active", link.getAttribute("href") === `#${entry.target.id}`));
  }
}), { rootMargin: "-35% 0px -58%", threshold: 0 });
sections.forEach((section) => sectionObserver.observe(section));

document.querySelector("#currentYear").textContent = new Date().getFullYear();

if (typeof window.createPascalHeroSimulation === "function") {
  window.pascalHeroSimulation = window.createPascalHeroSimulation();
}
