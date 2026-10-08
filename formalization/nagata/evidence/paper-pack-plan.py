from pathlib import Path
import json
base=Path(__file__).resolve().parents[1];site=base/'atlas'
plan=[
 ('1','有效曲线与射影点','Effective curves and projective points','Configuration Forms HomogeneousIdeals EffectiveCurves IdealCycles CycleMultiplicity ProjectiveMultiplicity ProjectiveTopology Homogenization HomogeneousFamilies'),
 ('2.1','闭关联与非常一般点','Closed incidence and very general points','Incidence UniversalFamilies UniversalSections PolynomialAvoidance Avoidance'),
 ('2.1','通用等重数归约','Universal equal-multiplicity reduction','UniversalReduction ArithmeticReduction'),
 ('2.2','局部重数与 Taylor 喷射','Local multiplicity and Taylor jets','AffineMultiplicity ChartJets ChartMultiplicityBridge FrechetMultiplicity HomogeneousOrder AnalyticOrder AnalyticJets AnalyticTaylor TaylorMultiplicity JetGerms AnalyticFactorization AnalyticScaling'),
 ('2.2','向法丛特化','Specialization to the normal bundle','NormalSpecialization MovingConfigurations NormalCharts CoverNormal Gluing GraphOrder DividedFamilies'),
 ('2.2','必要的法向多项式','Necessary normal polynomials','NormalPolynomials NecessarySections SectionOrder'),
 ('2.3','平方点数情形','The square case','SquareLinear SquareNormal SquareReduction LineBases LineConfigurations LineGeometry LineIntersections LineNormalData LineObstructions LineRestriction LineSmoothness MovingLines'),
 ('2.4','三次曲线上的九个零位移','Nine zero displacements on a cubic','LowDegree MarkedDisplacements MarkedPoints'),
 ('3.1','移除系数的强制零点','Removing forced coefficient zeros','CoefficientIdeals NormalCoefficients CoefficientBlocks Multipliers'),
 ('3.1','坐标变换与系数丛','Coordinate changes and coefficient bundles','CoefficientTransforms AssociatedBundles PolynomialBlocks MultiplierBundles QuotientSections CoefficientSpaces'),
 ('3.2','Theta 乘积与收敛','Theta products and convergence','ThetaProducts InfiniteProducts Automorphic GaussianBounds'),
 ('3.2','Laurent 系数与截面基','Laurent coefficients and section bases','ThetaCoefficients ThetaSeries LaurentCoefficients Fourier'),
 ('3.2','光滑平面三次曲线','Smooth plane cubics','CubicEquations CubicGeometry CubicMap CubicRelations CubicEvaluation Factorization BinaryForms'),
 ('3.3','选取三次曲线与标记点','Choosing the cubic and marked points','MarkedCubic TorusConfigurations TorusCharts Parameters RelationIdeals'),
 ('4.1','固定曲面上的点碰撞','Collision on a fixed surface','Collision GeometricCollision CollisionBounds SectionKernels FixedCurveSections RationalKernels'),
 ('4.2','共同坐标图','A common coordinate chart','ChartGradients'),
 ('4.2','归一化 Theta 截面','Normalized theta sections','ThetaSections ThetaLimits ThetaEvaluation'),
 ('4.3','多项式空间的基','Bases for polynomial spaces','PolynomialBases PolynomialJets ThetaPolynomialBases SectionBases ConstantSections SectionDimensions ThetaExponents'),
 ('4.4','极限喷射矩阵','The limiting jet matrix','ExponentMatrices MixedDerivatives ScaledMatrices MatrixLimits KernelBridges ThetaMatrices'),
 ('5.1','按水平行插值','Interpolation by horizontal rows','Interpolation Rows RowData'),
 ('5.2','指数集合的包围多边形','An enclosing polygon for exponents','Enclosure ExponentSets NormalizedExponents'),
 ('5.3','水平切片与整数行数','Horizontal slices and integer row counts','Intervals'),
 ('5.4','非抵消与满列秩矛盾','Noncancellation and the full-rank contradiction','BasisNoncancellation'),
 ('5.4 / 1.1','装配最终严格不等式','Assembling the final strict inequality','FullTarget Nagata')]
graph=json.loads((site/'lean-graph.json').read_text(encoding='utf-8'));nodes=graph['nodes']
available={Path(n['file']).stem for n in nodes};used=set();packs=[]
for index,(section,zh,en,files) in enumerate(plan):
    names=files.split();assert not used.intersection(names),(index,used.intersection(names));used.update(names)
    members=[n for n in nodes if Path(n['file']).stem in names]
    assert len(members)>=2,(index,names)
    packs.append({'id':'paper-'+str(index+1),'section':section,'titles':['§'+section+' '+zh,'§'+section+' '+en],
      'files':sorted({n['file'] for n in members}),'members':[n['id'] for n in members],'mainMembers':sum(n['inMainProof'] for n in members),
      'mapping':'Paper-section implementation grouping, not a new theorem or a claim of line-by-line equivalence.'})
assert available<=used,'Unassigned files: '+str(available-used)
assert sum(len(p['members']) for p in packs)==len(nodes)
graph['paperPacks']=packs
(site/'lean-graph.json').write_text(json.dumps(graph,ensure_ascii=False,separators=(',',':')),encoding='utf-8',newline='\n')
audit=json.loads((site/'audit.json').read_text(encoding='utf-8'));audit['paperPacks']=packs
audit['displayPolicy']={'organization':'paper sections and actual Lean source modules','paperPackCount':len(packs),'allProjectConstantsAssignedOnce':True,'actualCompilerDependenciesPreserved':True,'mathlibCodeExcluded':True}
(site/'audit.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2),encoding='utf-8',newline='\n')
print('Paper layout:',len(packs),'packs;',len(available),'source modules; every project constant assigned once.')
