const translations = {
  zh: {
    navResearch:"学术研究",navPubs:"论文",navContact:"联系",
    heroKicker:"华东师范大学 · 数学科学学院教授",heroLine1:"结构、动力，",heroLine2:"与智能发现。",
    heroIntro:"我研究代数几何与动力系统，并探索人工智能如何辅助数学推理、拓展战略世界与交互体验。",exploreResearch:"探索研究",playGame:"试玩《疆域争锋》",
    coreFields:"2023 年以来的近期论文",phdYear:"新加坡国立大学数学博士",openQuestions:"开放问题，严谨方法",newFrontiers:"数学与游戏的新边界",
    researchTitle:"近期论文与预印本。",researchLead:"学术研究区只呈现论文本身，并将最新 arXiv 记录置于最前。",viewArxiv:"在 arXiv 查看作者检索结果",
    agTitle:"代数几何",agText:"射影簇、典范除子、环面结构与几何分类。",bgTitle:"双有理几何",bgText:"极小模型纲领、有理连通簇与结构分解。",dsTitle:"动力系统",dsText:"满射自同态、算术度、稠密轨道与动力刚性。",
    currentProgram:"当前研究计划",programText:"满射自同态的分类及其在算术动力系统中的应用，包括 Kawaguchi–Silverman 猜想与 Zariski 稠密轨道猜想。",
    exploratory:"探索方向",aiMathTitle:"让 AI 成为数学探索的伙伴。",aiMathLead:"研究机器智能如何辅助而非替代形式推理、猜想生成、文献导航与数学交流。",
    formalReasoning:"形式推理",formalText:"证明辅助、验证闭环与可解释的数学论证链。",conjectureDiscovery:"猜想发现",conjectureText:"通过计算实验发现值得证明的模式与值得理解的反例。",knowledgeSystems:"数学知识系统",knowledgeText:"结构化连接定义、定理、例子与依赖图谱。",
    creativeLab:"创意实验室",aiGamesTitle:"把游戏变成策略与智能的实验室。",aiGamesLead:"可玩系统让抽象规则变得可见。AI4Games 探索战略智能体、程序化世界，以及把数学结构转化为交互的游戏机制。",
    gameTitle:"疆域争锋",gameText:"从零构建的即时领地策略游戏：连通路径、多建筑指挥、进化式箭塔能力、自适应电脑军团与八张战役地图。",gameFeature1:"拖拽指挥与框选",gameFeature2:"五类建筑自由改建",gameFeature3:"本地账号与持久化战役进度",launchGame:"进入游戏",
    agentText:"在局部控制、资源压力与网络变化中的决策。",proceduralText:"生成有意义差异的规则，而非装饰性的随机。",learningText:"通过交互理解网络、动力系统与优化。",
    publicationsTitle:"代表论文。",publicationsLead:"涵盖极化自同态、算术动力系统、双有理几何与紧复空间。",downloadCV:"下载简历",allPublications:"查看完整论文列表",
    journeyTitle:"学术经历。",ecnuRole:"数学科学学院教授 / 青年研究员",kiasRole:"研究员",mpiRole:"博士后研究员",nusRole:"数学博士 · 导师：张德祺",
    contactTitle:"一起探索一个困难问题。",contactLead:"欢迎就数学研究、学生培养以及数学、AI 与游戏的跨学科想法交流。",office:"办公室",institution:"单位",address:"地址",footerText:"数学 · 人工智能 · 游戏"
  }
};
const defaultText = new Map();
document.querySelectorAll("[data-i18n]").forEach((node)=>defaultText.set(node.dataset.i18n,node.textContent));
let language = "en";
const languageButton = document.querySelector("#languageButton");
languageButton.addEventListener("click",()=>{
  language = language === "en" ? "zh" : "en";
  document.documentElement.lang = language === "zh" ? "zh-CN" : "en";
  document.querySelectorAll("[data-i18n]").forEach((node)=>{
    node.textContent = language === "zh" ? translations.zh[node.dataset.i18n] || defaultText.get(node.dataset.i18n) : defaultText.get(node.dataset.i18n);
  });
  languageButton.textContent = language === "zh" ? "EN" : "中文";
});
const menuButton = document.querySelector("#menuButton");
const nav = document.querySelector("#mainNav");
menuButton.addEventListener("click",()=>{
  const open = nav.classList.toggle("open");
  menuButton.setAttribute("aria-expanded",String(open));
});
nav.querySelectorAll("a").forEach((link)=>link.addEventListener("click",()=>{nav.classList.remove("open");menuButton.setAttribute("aria-expanded","false");}));
const revealObserver = new IntersectionObserver((entries)=>entries.forEach((entry)=>{if(entry.isIntersecting){entry.target.classList.add("visible");revealObserver.unobserve(entry.target);}}),{threshold:.12});
document.querySelectorAll(".reveal").forEach((node)=>revealObserver.observe(node));
const sections = [...document.querySelectorAll("main section[id]")];
const navLinks = [...nav.querySelectorAll("a[href^='#']")];
const sectionObserver = new IntersectionObserver((entries)=>entries.forEach((entry)=>{if(entry.isIntersecting){navLinks.forEach((link)=>link.classList.toggle("active",link.getAttribute("href") === `#${entry.target.id}`));}}),{rootMargin:"-35% 0px -58%",threshold:0});
sections.forEach((section)=>sectionObserver.observe(section));
document.querySelector("#currentYear").textContent = new Date().getFullYear();
