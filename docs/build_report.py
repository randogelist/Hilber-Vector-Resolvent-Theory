#!/usr/bin/env python3
"""Rebuild the six-page report. Requires reportlab and DejaVu fonts; runs no Lean."""
from pathlib import Path
import argparse
from reportlab.pdfgen import canvas
from reportlab.lib.colors import HexColor, white
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import Paragraph
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,default=HERE/'RH_H00_Two_Routes_Native_PASS_and_GitHub_CI.pdf')
args=parser.parse_args()
args.output.parent.mkdir(parents=True,exist_ok=True)
FONT=Path('/usr/share/fonts/truetype/dejavu')
for name,file in [('Sans','DejaVuSans.ttf'),('Bold','DejaVuSans-Bold.ttf'),('Serif','DejaVuSerif.ttf'),('Mono','DejaVuSansMono.ttf')]:
    pdfmetrics.registerFont(TTFont(name,str(FONT/file)))
pdfmetrics.registerFontFamily('Sans',normal='Sans',bold='Bold',italic='Sans',boldItalic='Bold')
NAVY=HexColor('#123041'); TEAL=HexColor('#127C82'); INK=HexColor('#20343F'); MUTED=HexColor('#60757E'); PALE=HexColor('#EAF3F3'); LINE=HexColor('#CDDADF'); AMBER=HexColor('#A36017')
W,H=595.276,841.89; X=51; CW=W-102
C=canvas.Canvas(str(args.output),pagesize=(W,H),pageCompression=1)
C.setTitle('Two conditional routes from H00 to the Riemann Hypothesis')
C.setAuthor('Hilber-Vector-Resolvent-Theory project')
C.setSubject('Native PASS checkpoint and GitHub CI setup; H00 remains a hypothesis')
C.setCreator('ReportLab; reproducible docs/build_report.py')
S={
 'body':ParagraphStyle('body',fontName='Sans',fontSize=9.3,leading=14.4,textColor=INK,spaceAfter=9),
 'small':ParagraphStyle('small',fontName='Sans',fontSize=7.8,leading=11.3,textColor=MUTED),
 'code':ParagraphStyle('code',fontName='Mono',fontSize=7.6,leading=11.6,textColor=INK,wordWrap='CJK'),
 'formula':ParagraphStyle('formula',fontName='Sans',fontSize=11.2,leading=18,textColor=NAVY),
 'label':ParagraphStyle('label',fontName='Bold',fontSize=8.3,leading=12,textColor=TEAL),
}
page=0; y=0

def p(text,style='body',gap=8,x=X,width=CW):
    global y
    obj=Paragraph(text,S[style]); _,h=obj.wrap(width,1000)
    obj.drawOn(C,x,y-h); y-=h+gap
    if y<55: raise RuntimeError(f'Page {page} overflow: {y}')

def h(title):
    global y
    C.setFont('Bold',13); C.setFillColor(NAVY); C.drawString(X,y-13,title);y-=27

def tag(text):p(text.upper(),'label',gap=6)

def formula(text):
    global y
    obj=Paragraph(text,S['formula']); _,hh=obj.wrap(CW-26,1000)
    C.setFillColor(PALE); C.roundRect(X,y-hh-19,CW,hh+19,6,fill=1,stroke=0)
    obj.drawOn(C,X+13,y-hh-8); y-=hh+31

def code(text):p(text,'code',gap=10)

def refs(items):
    global y
    C.setStrokeColor(LINE); C.line(X,y-3,W-X,y-3);y-=15
    p('<b>Source anchors</b> · '+items,'small',gap=0)

def newpage(kicker,title,subtitle=None):
    global page,y
    if page:C.showPage()
    page+=1
    C.setFillColor(NAVY);C.rect(0,H-9,W,9,fill=1,stroke=0)
    C.setFont('Bold',7.4);C.setFillColor(TEAL);C.drawString(X,H-38,'HILBER-VECTOR-RESOLVENT-THEORY')
    C.setFont('Sans',7.4);C.setFillColor(MUTED);C.drawRightString(W-X,H-38,'28 OCTOBER 2026')
    C.setStrokeColor(LINE);C.line(X,43,W-X,43)
    C.setFont('Sans',6.8);C.setFillColor(MUTED);C.drawString(X,30,'ZETA_HYPERBOLIC_ANCHOR_5  ·  A_TIER_LEAN')
    C.drawRightString(W-X,30,f'{page} / 6')
    y=H-69;tag(kicker)
    C.setFillColor(NAVY);C.setFont('Bold',23);C.drawString(X,y-23,title);y-=39
    if subtitle:p(subtitle,'small',gap=16)

newpage('Verified conditional constructions','Two routes from H00 to RH', 'A mathematical and reproducibility record for the v0.2.3 native checkpoint.')
p('The project supplies two forward constructions from the same semantic zero-cancellation hypothesis to Mathlib’s literal Riemann Hypothesis. Each is paired with the retained converse. The native run is reported as compiled and axiom-audited; GitHub CI is a new, separately tracked verification target.')
formula('H<sub>00</sub> ⇔ RiemannHypothesis')
h('The exact Lean endpoints')
p('All four declarations live in the namespace <font name="Mono">RH_HilbertLimit.TwoRoutes</font>.')
code('nativeRH_of_H00_route_one :<br/>  H00 → _root_.RiemannHypothesis<br/><br/>H00_iff_nativeRH_route_one :<br/>  H00 ↔ _root_.RiemannHypothesis<br/><br/>nativeRH_of_H00_route_two :<br/>  H00 → _root_.RiemannHypothesis<br/><br/>H00_iff_nativeRH_route_two :<br/>  H00 ↔ _root_.RiemannHypothesis')
h('Two forward constructions, shared foundations')
p('<b>Route 1:</b> zero cancellation gives constant Bernstein-row variation, then subexponential growth and the retained actual spectral closure.')
p('<b>Route 2:</b> row positivity constructs a probability measure with the actual moments. Its analytic resolvent identifies the actual logarithmic derivative and excludes nonreal zeros.')
p('The second forward proof does not call Route 1’s RH endpoint. It does use shared finite positivity lemmas. Both equivalence declarations use the same retained RH-to-H00 converse.')
p('<b>Scope boundary.</b> H00 is assumed, not established. No finite accepted certificate or unconditional proof of RH is claimed. The original longer Widder/angular-PDE chain remains a separate, unfinished formalization.')
refs('RH_HilbertLimit/TwoRoutes/RouteOne.lean; RouteTwo.lean; native PASS companion checkpoint.')

newpage('01 / Exact premise','Finite data, universal validity','The zero-budget pair is finite. Its admissibility is an all-order proposition.')
p('Let Θ denote <font name="Mono">AWPIRH.theta</font>, the project’s actual entire theta function. Its logarithmic derivative and normalized real moments are the unchanged objects used by both routes:')
formula('R(z) = Θ′(z) / Θ(z)<br/>m<sub>n</sub> = Re[(-1)<super>n</super> R<super>(n)</super>(0) / n!]<br/>κ = m<sub>0</sub> &gt; 0, &nbsp;&nbsp; u<sub>n</sub> = m<sub>n</sub> / κ<super>n+1</super>, &nbsp;&nbsp; u<sub>0</sub> = 1')
p('Reality of the complex moments is supplied by the retained Schwarz-reflection result. Positivity of κ and the degree-zero normalization are unconditional ingredients, not additional assumptions of either endpoint.')
h('Bernstein rows and cancellation')
formula('w<sub>N,j</sub> = binom(N,j) ∑<sub>r=0</sub><super>N-j</super> (-1)<super>r</super> binom(N-j,r) u<sub>j+r</sub><br/>V<sub>N</sub> = ∑<sub>j=0</sub><super>N</super> |w<sub>N,j</sub>|<br/>C<sub>n</sub> = (n+1)(V<sub>n+1</sub> - V<sub>n</sub>) ≥ 0')
p('Here C<sub>n</sub> is <font name="Mono">rowCancellation</font>. The displayed variation identity is proved by finite Bernstein coarsening. The named candidate is exactly the natural-number pair with cutoff 0 and coefficient 0.')
code('def H00 : Prop := zeroBudgetCandidate.Admissible')
p('For a budget W, admissibility means every n at or beyond W.cutoff satisfies C<sub>n</sub> ≤ W.coefficient · V<sub>n</sub>. Thus the candidate (0,0) requires all C<sub>n</sub> to vanish:')
formula('H<sub>00</sub> ⇔ (∀n, C<sub>n</sub> = 0)<br/>⇔ (∀N, V<sub>N</sub> = 1)<br/>⇔ (∀N, ∀j ≤ N, w<sub>N,j</sub> ≥ 0)')
p('These are semantic equivalences. A finite list of successful rows does not establish the universal condition. The required propagation or checker argument remains open.','small')
refs('ActualXi.lean; Bernstein.lean; Cancellation.lean; ActualCancellationWitness.lean; ZeroBudgetCandidate.lean; TwoRoutes/RouteOne.lean.')

newpage('02 / Route 1','Cancellation to spectral closure','The forward chain begins with exact finite identities and ends at the retained actual spectral theorem.')
h('1. Every variation increment vanishes')
p('H00 gives C<sub>n</sub> = 0 at every index. Since n+1 is positive, the cancellation identity forces V<sub>n+1</sub> = V<sub>n</sub>. Induction from the unconditional V<sub>0</sub> = 1 gives V<sub>n</sub> = 1 for all n.')
code('actual_variation_one_of_H00<br/>actual_weights_nonnegative_of_H00')
p('The row-mass identity and unit total variation also force every Bernstein weight to be nonnegative. This finite consequence is the common input used by Route 2.')
h('2. Unit variation is subexponential')
formula('∀ε &gt; 0, &nbsp; ∀n ≥ 0, &nbsp; V<sub>n</sub> = 1 ≤ exp(εn)')
p('The source supplies the constant 1 in the definition of <font name="Mono">Subexponential actualVariation</font>. There is no extra growth premise and no numerical asymptotic test.')
code('actual_subexponential_of_H00')
h('3. Apply the actual spectral equivalence')
p('The retained theorem <font name="Mono">canonical_actual_subexponential_iff_nativeRH</font> identifies subexponential actual variation with literal Mathlib RH. The route invokes its forward direction on the bound just derived.')
code('theorem nativeRH_of_H00_route_one (h : H00) :<br/>    _root_.RiemannHypothesis := by<br/>  exact canonical_actual_subexponential_iff_nativeRH.mp<br/>    (actual_subexponential_of_H00 h)')
h('The converse is shared')
p('The retained RH-to-zero-cancellation construction supplies <font name="Mono">H00_of_nativeRH</font>. Pairing it with this forward proof yields <font name="Mono">H00_iff_nativeRH_route_one</font>. Route 2 uses the same converse only when forming its own equivalence.')
refs('TwoRoutes/RouteOne.lean; ZeroBudgetCandidate.lean; ActualCancellationWitness.lean; retained actual spectral closure imported by these modules.')

newpage('03 / Route 2: measure construction','Positive rows become a measure','The measure is constructed from H00; it is not an additional existence hypothesis.')
h('1. Positive finite averages')
p('For positive Bernstein rows, the finite averages have total mass one. Writing q<sub>N,j</sub> = j/N for N &gt; 0, define the corresponding finite quadrature on [0,1]:')
formula('A<sub>N</sub>(f) = ∑<sub>j=0</sub><super>N</super> w<sub>N,j</sub> f(q<sub>N,j</sub>)<br/>A<sub>N</sub>(1) = 1, &nbsp; A<sub>N</sub>(f) ≥ 0 if f ≥ 0<br/>|A<sub>N</sub>(f)| ≤ ‖f‖<sub>∞</sub>')
p('The degree-zero definition is handled in the source; it does not affect the limit at infinity. The exact Bernstein monomial identity gives A<sub>N</sub>(q ↦ q<super>k</super>) → u<sub>k</sub> for each k.')
code('bernsteinAverage_monomial_tendsto')
h('2. A positive functional on continuous functions')
p('Compact bounds permit a hyperfilter limit of the finite averages for each continuous f. Linearity, positivity and normalization pass to the limit. The result is a positive linear functional L on C([0,1], ℝ), with L(1) = 1.')
p('This is a classical, noncomputable construction. It is compatible with the stated axiom allowlist; it does not turn H00 into a terminating decision procedure.')
h('3. Riesz representation and exact moments')
p('Mathlib’s real Riesz representation theorem constructs the representing measure σ. Normalization gives total mass one. The independently proved monomial limit identifies all its moments:')
formula('σ([0,1]) = 1, &nbsp; σ ≥ 0<br/>∫<sub>[0,1]</sub> q<super>k</super> dσ(q) = u<sub>k</sub> &nbsp; for every k ∈ ℕ')
code('actualHausdorffMeasure (h : H00)<br/>actualHausdorffMeasure_isProbabilityMeasure<br/>actualHausdorffMeasure_moment')
p('The actual measure is obtained by instantiating the generic construction with u = actualNormalizedMoment and the positivity already derived from H00. No output of the first RH closure is used.')
refs('TwoRoutes/BernsteinMomentLimit.lean; HausdorffMeasure.lean; shared finite positivity lemmas in RouteOne.lean and PositiveMomentBridge.lean.')

newpage('04 / Route 2: analytic closure','The resolvent excludes nonreal zeros','The continuation step uses an analytic defect across possible zeros of Θ.')
h('1. Form the positive resolvent')
formula('S(z) = κ ∫<sub>[0,1]</sub> 1 / (1 + κqz) dσ(q)<br/>Im S(z) ≤ 0 &nbsp; whenever Im z &gt; 0')
p('Compact support gives analyticity near zero and throughout the upper half-plane. The kernel has nonpositive imaginary part there, and integration preserves this sign.')
h('2. Identify the actual germ')
formula('S<super>(n)</super>(0) = (-1)<super>n</super> n! κ<super>n+1</super> u<sub>n</sub> = R<super>(n)</super>(0)')
p('Both functions are analytic near zero, where Θ(0) ≠ 0. Equality of all derivatives identifies their convergent Taylor germs. The source uses analytic power series, rather than merely comparing formal coefficients.')
code('actual_logDerivative_resolvent_germ')
h('3. Continue the analytic defect')
formula('D(z) = Θ′(z) - S(z)Θ(z)')
p('D is analytic on the connected upper half-plane and vanishes on an open portion supplied by the origin germ. The identity theorem gives D = 0 there. This argument does not assume that Θ is zero-free in order to continue Θ′/Θ.')
h('4. Exclude nonreal zeros and conclude RH')
p('At points where Θ is nonzero, D = 0 gives R = S and hence Im R ≤ 0. A zero of multiplicity m in the upper half-plane would create the local logarithmic-derivative pole m/(z-α). Probing immediately below that zero forces a positive imaginary part, contradicting the sign bound. Conjugation symmetry excludes lower-half-plane zeros, and the retained actual-theta zero bridge concludes literal RH.')
code('nativeRH_of_H00_via_measure_resolvent<br/>nativeRH_of_H00_route_two')
p('All analytic and measure obligations in this compressed route are supplied internally. The original Widder/angular-PDE route is not certified by this replacement.','small')
refs('TwoRoutes/MeasureResolvent.lean; ResolventAnalytic.lean; ActualResolventContinuation.lean; ActualHerglotzClosure.lean; RouteTwo.lean.')

newpage('05 / Evidence and reproduction','What is verified, and where','Native evidence is preserved. GitHub CI is a separate target with its own run artifacts.')
h('Native checkpoint: user-reported PASS')
p('The supplied console excerpt reports <font name="Mono">PROJECT_BUILD=PASS</font> and <font name="Mono">RUN=PASS</font>: 3 modules compiled and 115 reused. The preserved plan contains 117 source modules plus the final audit source, with 641 selected declarations. Inspection of that plan confirms coverage of both endpoints and both equivalences.')
p('The checkpoint records that native logs and receipts were <b>not independently read</b>. Exact per-declaration axiom lists are absent from the supplied excerpt. Native success is therefore recorded as reported by the user, supported by audit-plan and runner inspection.')
h('New target: GitHub CI')
p('The CI setup pins Lean 4.33.0 and mathlib’s v4.33.0 commit. The native mathlib commit was not supplied; this is a new reproducible CI baseline. GitHub Actions builds the preserved sources, runs the final axiom audit and retains logs. Missing declarations, malformed output and unexpected axioms must fail the audit.')
code('Lean: leanprover/lean4:v4.33.0<br/>Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d<br/>Allowed: propext, Classical.choice, Quot.sound')
p('<b>Publication status:</b> GitHub CI is newly configured. This report does not assert a CI PASS; consult the workflow run associated with the repository commit. Native receipts are not substituted for a GitHub CI result.')
p('<link href="https://github.com/randogelist/Hilber-Vector-Resolvent-Theory" color="#127C82">Repository: randogelist/Hilber-Vector-Resolvent-Theory</link><br/><link href="https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/actions" color="#127C82">Live GitHub Actions runs and audit artifacts</link>','small',gap=11)
h('Preserved package identity')
p('RH_H00_TWO_ROUTES_LEAN_v0_2_3_construction.zip','code',gap=3)
code('SHA-256:<br/>578cc8ad072c79dc7838fcf65a27b9eed<br/>707fcc98e0fdf6a4b3601aa20e8c51a')
h('Open obligations')
p('H00 admissibility and all-order propagation; a terminating finite checker with soundness and completeness; an accepted finite witness; the accepted-witness/RH equivalence; and the longer Widder/angular-PDE chain. Unconditional RH is not established.')
p('The native package stays unchanged; its preparation-status headers predate the newer PASS checkpoint. The exact anchor ZETA_HYPERBOLIC_ANCHOR_5 is preserved. No new Init record or local Lean/Lake execution was used to prepare this report and setup.','small')
refs('RH_H00_TWO_ROUTES_LEAN_v0_2_3_NATIVE_PASS_CHECKPOINT.json; TwoRoutesAudit.lean; audit-targets.tsv; compile-order.txt; pinned CI configuration.')
C.save()
print(args.output)
