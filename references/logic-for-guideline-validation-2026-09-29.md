# Which logic for formally validating clinical practice guidelines?

Literature search, 2026-09-29. Question: which logic, or combination of logics, is most
valuable to implement for consistency checking and conflict detection between guideline
recommendations, for the `guideline-validation` project (LLM-extracted obligations, checked
with deontic STIT (G3DS) and KD tableaux; temporal constraints currently dropped; ~14% of
obligations carry timing).

**Method.** PubMed E-utilities (free-text and title searches), Crossref bibliographic
search, OpenAlex and Semantic Scholar for abstracts of CS papers not in PubMed, and
institutional repositories (VU Amsterdam, Utrecht, Haifa) for abstracts and green copies.
Every paper below was verified by DOI against Crossref (title, authors, venue, pages);
the eight biomedical-venue papers were also matched to a PubMed record. Open access was
checked by PMC link (`linkname=pubmed_pmc`), then Unpaywall.

**Verification tally:** 13 papers, 13 verified by Crossref DOI (8 also by PubMed), 0
unverifiable. Two carry caveats: `sanati2014` has no retrievable abstract (the publisher
elides it from every API and Springer's page is behind a bot challenge), and
`governatori2007` has no year in Crossref's `issued` field (year 2007 comes from OpenAlex,
Semantic Scholar and the VU repository, and the volume is the AI 2007 proceedings).

Thirteen papers is over the 8–10 target: the candidate list spans nine families, and two
are reviews. The core set, if you want ten, drops `bilici2018`, `broersen2004` and
`hommersom2007`.

---

## Part 1 — Summary table

| # | Key | Authors (Year) | Title (shortened) | Venue | Access | Logic / candidate | Why it's relevant |
|---|-----|----------------|-------------------|-------|--------|-------------------|-------------------|
| 1 | peleg2013 | Peleg (2013) | Computer-interpretable clinical guidelines: a methodological review | J Biomed Inform | Bronze (Elsevier); PDF blocked | Review of CIGs | Standard methodological review; names V&V and temporal expressions as themes |
| 2 | bilici2018 | Bilici, Despotou, Arvanitis (2018) | CIGs to manage care complexities in multimorbidity: a review | Digital Health | Gold OA (CC BY-NC-ND), PMC6172935; PDF blocked (403) | Review, multimorbidity | Reviews 2011–2017 conflict detection and temporal-constraint handling across CIG CDSSs |
| 3 | bottrighi2010 | Bottrighi et al. (2010) | Adopting model checking techniques for clinical guidelines verification | Artif Intell Med | Paywalled | LTL model checking (GLARE + SPIN) | Finds inconsistencies in a stroke guideline that manual review missed |
| 4 | hommersom2007 | Hommersom et al. (2007) | Verification of medical guidelines using background knowledge in task networks | IEEE TKDE | Paywalled | Asbru task networks, KIV theorem prover | Asbru verification with medical background knowledge (diabetes type 2) |
| 5 | anselma2006 | Anselma et al. (2006) | Repetitions, periodicity and temporal constraints in clinical guidelines | Artif Intell Med | Paywalled | Temporal constraint networks (GLARE) | Durations, delays and periodic repetition with a correct, complete, tractable consistency check |
| 6 | sanati2014 | Yousef Sanati, MacCaull, Maibaum (2014) | Analyzing CPGs using a decidable metric interval-based temporal logic | FM 2014, LNCS 8442 | Paywalled | Metric interval temporal logic | Decidable metric interval logic; guideline consistency as satisfiability |
| 7 | guo2016 | Guo et al. (2016) | Transforming medical best practice guidelines to verifiable statechart models | ICCPS 2016 (IEEE) | Paywalled | Timed automata, UPPAAL | Guideline statecharts compiled to timed automata and checked in UPPAAL |
| 8 | mulyar2008 | Mulyar, Pesic, van der Aalst, Peleg (2008) | Declarative and procedural approaches for modelling clinical guidelines | BPM Workshops 2007, LNCS 4928 | Paywalled | Declare-style LTL constraints (CIGDec) | Declarative constraint language for guidelines, the Declare family applied to CIGs |
| 9 | governatori2007 | Governatori, Hulstijn, Riveret, Rotolo (2007) | Characterising deadlines in temporal modal defeasible logic | AI 2007, LNCS 4830 | Green (VU repository); PDF blocked (403) | Temporal deontic defeasible logic | Typology of deadline obligations: operator, achievement vs maintenance, sanctions, persistence |
| 10 | broersen2004 | Broersen, Dignum, Dignum, Meyer (2004) | Designing a deontic logic of deadlines | DEON 2004, LNCS 3065 | Green (Utrecht); **PDF saved** | Deadline obligations in branching time (CTL) | Deadline obligation O(ρ ≤ δ) over branching-time models, the STIT frame class |
| 11 | zamborlini2017 | Zamborlini et al. (2017) | Analyzing interactions on combining multiple clinical guidelines | Artif Intell Med | Bronze (Elsevier); PDF blocked | Semantic web / TMR model with rules | Reusable rules detect interactions between recommendations from several guidelines |
| 12 | michalowski2021 | Michalowski, Wilk, Michalowski, Carrier (2021) | MitPlan: a planning approach to mitigating concurrently applied CPGs | Artif Intell Med | Paywalled | FOL then PDDL durative planning | Successor to the FOL mitigation framework; timed actions and planning horizons |
| 13 | piovesan2020 | Piovesan, Terenziani, Theseider Dupré (2020) | Conformance analysis for comorbid patients in ASP | J Biomed Inform | Bronze (Elsevier); PDF blocked | Answer set programming | Comorbid CIG interactions and deviations in ASP, with a temporal treatment |

Screened out (⚠️ maybe, not included): Pérez & Porres 2010, *Authoring and verification of
clinical guidelines: a model driven approach*, JBI 43(4):520–536, doi:10.1016/j.jbi.2010.02.009
(UML statecharts plus a model checker; its abstract does not name the checker, so it was
not usable as the UPPAAL example); Rovani et al. 2015, *Declarative process mining in
healthcare*, Expert Syst Appl, doi:10.1016/j.eswa.2015.07.040 (Declare, but used for process
mining, not guideline consistency); Jafarpour et al. 2019, AIM, doi:10.1016/j.artmed.2019.02.003
(OWL execution-time guideline merging); Wilk et al.'s FOL mitigation papers (MitPlan's
abstract describes them as its predecessor). De Giacomo & Vardi's LTLf paper (IJCAI 2013)
is the seminal LTLf source but was not retrieved or verified here, so no cell cites it.

---

## Part 2 — BibTeX

```bibtex
@article{peleg2013,
  author  = {Peleg, Mor},
  title   = {Computer-interpretable clinical guidelines: A methodological review},
  journal = {Journal of Biomedical Informatics},
  year    = {2013},
  volume  = {46},
  number  = {4},
  pages   = {744--763},
  doi     = {10.1016/j.jbi.2013.06.009}
}

@article{bilici2018,
  author  = {Bilici, Eda and Despotou, George and Arvanitis, Theodoros N.},
  title   = {The use of computer-interpretable clinical guidelines to manage care complexities of patients with multimorbid conditions: A review},
  journal = {Digital Health},
  year    = {2018},
  volume  = {4},
  pages   = {2055207618804927},
  doi     = {10.1177/2055207618804927}
}

@article{bottrighi2010,
  author  = {Bottrighi, Alessio and Giordano, Laura and Molino, Gianpaolo and Montani, Stefania and Terenziani, Paolo and Torchio, Mauro},
  title   = {Adopting model checking techniques for clinical guidelines verification},
  journal = {Artificial Intelligence in Medicine},
  year    = {2010},
  volume  = {48},
  number  = {1},
  pages   = {1--19},
  doi     = {10.1016/j.artmed.2009.09.003}
}

@article{hommersom2007,
  author  = {Hommersom, Arjen and Groot, Perry and Lucas, Peter J. F. and Balser, Michael and Schmitt, Jonathan},
  title   = {Verification of Medical Guidelines Using Background Knowledge in Task Networks},
  journal = {IEEE Transactions on Knowledge and Data Engineering},
  year    = {2007},
  volume  = {19},
  number  = {6},
  pages   = {832--846},
  doi     = {10.1109/tkde.2007.190611}
}

@article{anselma2006,
  author  = {Anselma, Luca and Terenziani, Paolo and Montani, Stefania and Bottrighi, Alessio},
  title   = {Towards a comprehensive treatment of repetitions, periodicity and temporal constraints in clinical guidelines},
  journal = {Artificial Intelligence in Medicine},
  year    = {2006},
  volume  = {38},
  number  = {2},
  pages   = {171--195},
  doi     = {10.1016/j.artmed.2006.03.007}
}

@inproceedings{sanati2014,
  author    = {Yousef Sanati, Morteza and MacCaull, Wendy and Maibaum, Thomas S. E.},
  title     = {Analyzing Clinical Practice Guidelines Using a Decidable Metric Interval-Based Temporal Logic},
  booktitle = {FM 2014: Formal Methods},
  series    = {Lecture Notes in Computer Science},
  volume    = {8442},
  publisher = {Springer},
  year      = {2014},
  pages     = {611--626},
  doi       = {10.1007/978-3-319-06410-9_41}
}

@inproceedings{guo2016,
  author    = {Guo, Chunhui and Ren, Shangping and Jiang, Yu and Wu, Po-Liang and Sha, Lui and Berlin, Richard B.},
  title     = {Transforming Medical Best Practice Guidelines to Executable and Verifiable Statechart Models},
  booktitle = {2016 ACM/IEEE 7th International Conference on Cyber-Physical Systems (ICCPS)},
  publisher = {IEEE},
  year      = {2016},
  pages     = {1--10},
  doi       = {10.1109/iccps.2016.7479121}
}

@inproceedings{mulyar2008,
  author    = {Mulyar, Nataliya and Pesic, Maja and van der Aalst, Wil M. P. and Peleg, Mor},
  title     = {Declarative and Procedural Approaches for Modelling Clinical Guidelines: Addressing Flexibility Issues},
  booktitle = {Business Process Management Workshops (BPM 2007)},
  series    = {Lecture Notes in Computer Science},
  volume    = {4928},
  publisher = {Springer},
  year      = {2008},
  pages     = {335--346},
  doi       = {10.1007/978-3-540-78238-4_35}
}

@inproceedings{governatori2007,
  author    = {Governatori, Guido and Hulstijn, Joris and Riveret, R{\'e}gis and Rotolo, Antonino},
  title     = {Characterising Deadlines in Temporal Modal Defeasible Logic},
  booktitle = {AI 2007: Advances in Artificial Intelligence},
  series    = {Lecture Notes in Computer Science},
  volume    = {4830},
  publisher = {Springer},
  year      = {2007},
  pages     = {486--496},
  doi       = {10.1007/978-3-540-76928-6_50}
}

@inproceedings{broersen2004,
  author    = {Broersen, Jan and Dignum, Frank and Dignum, Virginia and Meyer, John-Jules Ch.},
  title     = {Designing a Deontic Logic of Deadlines},
  booktitle = {Deontic Logic in Computer Science (DEON 2004)},
  editor    = {Lomuscio, Alessio and Nute, Donald},
  series    = {Lecture Notes in Computer Science},
  volume    = {3065},
  publisher = {Springer},
  year      = {2004},
  pages     = {43--56},
  doi       = {10.1007/978-3-540-25927-5_5}
}

@article{zamborlini2017,
  author  = {Zamborlini, Veruska and da Silveira, Marcos and Pruski, Cedric and ten Teije, Annette and Geleijn, Edwin and van der Leeden, Marike and Stuiver, Martijn and van Harmelen, Frank},
  title   = {Analyzing interactions on combining multiple clinical guidelines},
  journal = {Artificial Intelligence in Medicine},
  year    = {2017},
  volume  = {81},
  pages   = {78--93},
  doi     = {10.1016/j.artmed.2017.03.012}
}

@article{michalowski2021,
  author  = {Michalowski, Martin and Wilk, Szymon and Michalowski, Wojtek and Carrier, Marc},
  title   = {MitPlan: A planning approach to mitigating concurrently applied clinical practice guidelines},
  journal = {Artificial Intelligence in Medicine},
  year    = {2021},
  volume  = {112},
  pages   = {102002},
  doi     = {10.1016/j.artmed.2020.102002}
}

@article{piovesan2020,
  author  = {Piovesan, Luca and Terenziani, Paolo and Theseider Dupr{\'e}, Daniele},
  title   = {Conformance analysis for comorbid patients in Answer Set Programming},
  journal = {Journal of Biomedical Informatics},
  year    = {2020},
  volume  = {103},
  pages   = {103377},
  doi     = {10.1016/j.jbi.2020.103377}
}
```

Volume numbers for the four LNCS chapters (8442, 4928, 4830, 3065) come from the proceedings
records found during search (Springer/dblp/repository citations), not from Crossref's
`/works/{DOI}` record, which omits them; check them before submission.

---

## Part 3 — Abstracts and key findings

PDF note for all Elsevier (sciencedirect.com), SAGE and VU-repository copies: each returned an
HTTP 403 "Just a moment..." Cloudflare challenge to `curl`. Not retried; fetch them by browser.
Unless stated, key findings come from the abstract only.

### peleg2013 — Peleg (2013)
**PMID:** 23806274 | **DOI:** 10.1016/j.jbi.2013.06.009 | **PMC:** none
**Access:** Unpaywall bronze (free to read at ScienceDirect, no license). **PDF:** tried, failed (403 Cloudflare, sciencedirect.com).

**Abstract:**
> Clinical practice guidelines (CPGs) aim to improve the quality of care, reduce unjustified practice variations and reduce healthcare costs. In order for them to be effective, clinical guidelines need to be integrated with the care flow and provide patient-specific advice when and where needed. Hence, their formalization as computer-interpretable guidelines (CIGs) makes it possible to develop CIG-based decision-support systems (DSSs), which have a better chance of impacting clinician behavior than narrative guidelines. This paper reviews the literature on CIG-related methodologies since the inception of CIGs, while focusing and drawing themes for classifying CIG research from CIG-related publications in the Journal of Biomedical Informatics (JBI). The themes span the entire life-cycle of CIG development and include: knowledge acquisition and specification for improved CIG design, including (1) CIG modeling languages and (2) CIG acquisition and specification methodologies, (3) integration of CIGs with electronic health records (EHRs) and organizational workflow, (4) CIG validation and verification, (5) CIG execution engines and supportive tools, (6) exception handling in CIGs, (7) CIG maintenance, including analyzing clinician's compliance to CIG recommendations and CIG versioning and evolution, and finally (8) CIG sharing. I examine the temporal trends in CIG-related research and discuss additional themes that were not identified in JBI papers, including existing themes such as overcoming implementation barriers, modeling clinical goals, and temporal expressions, as well as futuristic themes, such as patient-centric CIGs and distributed CIGs.

**Key findings (abstract only):** A thematic review of CIG methods, organized around the CIG
life cycle. Verification and validation is one of eight themes, and "temporal expressions" is
one of the themes it names as outside JBI's coverage. It is the reference for placing a new
verification logic among CIG languages, not a comparison of logics.

### bilici2018 — Bilici, Despotou, Arvanitis (2018)
**PMID:** 30302270 | **DOI:** 10.1177/2055207618804927 | **PMC:** PMC6172935 (PMC's OA web service returned 404 at check time; Unpaywall says gold, CC BY-NC-ND)
**PDF:** tried, failed: Europe PMC render and SAGE both returned 403 HTML.

**Abstract:**
> Clinical practice guidelines (CPGs) document evidence-based information and recommendations on treatment and management of conditions. CPGs usually focus on management of a single condition; however, in many cases a patient will be at the centre of multiple health conditions (multimorbidity). Multiple CPGs need to be followed in parallel, each managing a separate condition, which often results in instructions that may interact with each other, such as conflicts in medication. Furthermore, the impetus to deliver customised care based on patient-specific information, results in the need to be able to offer guidelines in an integrated manner, identifying and managing their interactions. In recent years, CPGs have been formatted as computer-interpretable guidelines (CIGs). This enables developing CIG-driven clinical decision support systems (CDSSs), which allow the development of IT applications that contribute to the systematic and reliable management of multiple guidelines. This study focuses on understanding the use of CIG-based CDSSs, in order to manage care complexities of patients with multimorbidity. The literature between 2011 and 2017 is reviewed, which covers: (a) the challenges and barriers in the care of multimorbid patients, (b) the role of CIGs in CDSS augmented delivery of care, and (c) the approaches to alleviating care complexities of multimorbid patients. Generating integrated care plans, detecting and resolving adverse interactions between treatments and medications, dealing with temporal constraints in care steps, supporting patient-caregiver shared decision making and maintaining the continuity of care are some of the approaches that are enabled using a CIG-based CDSS.

**Key findings (abstract only):** A 2011–2017 review of CIG-based CDSS for multimorbidity. It
lists "detecting and resolving adverse interactions between treatments and medications" and
"dealing with temporal constraints in care steps" as distinct approaches, which supports
treating conflict detection and temporal checking as separable layers.

### bottrighi2010 — Bottrighi et al. (2010)
**PMID:** 19864118 | **DOI:** 10.1016/j.artmed.2009.09.003 | **PMC:** none | **Access:** paywalled (Unpaywall closed). *Full text requires institutional access.*

**Abstract:**
> OBJECTIVES: Clinical guidelines (GLs) are assuming a major role in the medical area, in order to grant the quality of the medical assistance and to optimize medical treatments within healthcare organizations. The verification of properties of the GL (e.g., the verification of GL correctness with respect to several criteria) is a demanding task, which may be enhanced through the adoption of advanced Artificial Intelligence techniques. In this paper, we propose a general and flexible approach to address such a task. METHODS AND MATERIALS: Our approach to GL verification is based on the integration of a computerized GL management system with a model-checker. We propose a general methodology, and we instantiate it by loosely coupling GLARE, our system for acquiring, representing and executing GLs, with the model-checker SPIN. RESULTS: We have carried out an in-depth analysis of the types of properties that can be effectively verified using our approach, and we have completed an overview of the usefulness of the verification task at the different stages of the GL life-cycle. In particular, experimentation on a GL for ischemic stroke has shown that the automatic verification of properties in the model checking approach is able to discover inconsistencies in the GL that cannot be detected in advance by hand. CONCLUSION: Our approach thus represents a further step in the direction of general and flexible automated GL verification, which also meets usability requirements.

**Key findings (abstract only):** GLARE guidelines are translated to SPIN (LTL model checking),
loosely coupled. On an ischemic stroke guideline, automated verification found inconsistencies
not detectable by hand. This is the main evidence that model checking a CIG finds real errors;
it verifies guideline *structure and paths*, not deontic force.

### hommersom2007 — Hommersom et al. (2007)
**PMID:** none (IEEE, not indexed) | **DOI:** 10.1109/tkde.2007.190611 | **Access:** paywalled. *Full text requires institutional access.*
Abstract source: OpenAlex (reconstructed from its inverted index; publisher abstract, verbatim word order).

**Abstract:**
> The application of a medical guideline to the treatment of a patient's disease can be seen as the execution of tasks, sequentially or in parallel, in the face of patient data. It has been shown that many of such guidelines can be represented as a "network of tasks," that is, as a sequence of steps that have a specific function or goal. In this paper, a novel methodology for verifying the quality of such guidelines is introduced. To investigate the quality of such guidelines, we propose to include medical background knowledge to task networks and to formalize criteria for good medical practice that a guideline should comply with. This framework was successfully applied to a guideline dealing with the management of diabetes mellitus type 2 by using KIV.

**Key findings (abstract only):** Guidelines as task networks (the Asbru family), plus medical
background knowledge, plus formalized quality criteria, checked with the KIV interactive
theorem prover on a type 2 diabetes guideline. Unverified from the abstract: that the temporal
layer is an interval temporal logic; I recall this from the Protocure line of work, but the
abstract does not say it.

### anselma2006 — Anselma et al. (2006)
**PMID:** 16766167 | **DOI:** 10.1016/j.artmed.2006.03.007 | **PMC:** none | **Access:** paywalled. *Full text requires institutional access.*

**Abstract:**
> OBJECTIVE: In this paper, we define a principled approach to represent temporal constraints in clinical guidelines and to reason (i.e., perform inferences in the form of constraint propagation) on them. We consider different types of constraints, including composite and repeated actions, and propose different types of temporal functionalities (e.g., temporal consistency checking). BACKGROUND: Constraints about actions, durations, delays and periodic repetitions of actions are an intrinsic part of most clinical guidelines. Although several approaches provide expressive temporal formalisms, only few of them deal with the related temporal reasoning issues. METHODOLOGY: We first propose a temporal representation formalism and two temporal reasoning algorithms. Then, we consider the trade-off between the expressiveness of the formalism and the computational complexity of the algorithms, in order to devise a correct, complete and tractable approach. Finally, we show how the algorithms can be exploited to provide clinical guideline systems with different types of temporal facilities. RESULTS: Our approach offers several advantages. During the guideline acquisition phase, it enables to represent temporal constraints, and to check their consistency. In the execution phase, it checks the consistency between the execution times of the actions and the constraints in the guidelines, and provides query answering and simulation facilities.

**Key findings (abstract only):** A temporal constraint formalism for guideline actions covering
durations, delays, composite actions and *periodic repetitions*, with reasoning by constraint
propagation. The authors trade expressiveness against complexity to get a "correct, complete
and tractable" consistency check, usable both at acquisition time and against execution times.
This is the paper that most directly answers requirement (a) for guidelines.

### sanati2014 — Yousef Sanati, MacCaull, Maibaum (2014)
**PMID:** none | **DOI:** 10.1007/978-3-319-06410-9_41 | **Access:** paywalled (Unpaywall closed). *Full text requires institutional access.*

**Abstract:** Not retrievable. Crossref, OpenAlex and Semantic Scholar all report the abstract
as elided by the publisher, and Springer's page returned a bot challenge. Existence, authors,
title, venue and pages are verified via Crossref.

**What is known (search-engine summary of the Springer page, paraphrased, not verbatim):** the
paper develops a metric interval-based temporal logic for modeling guidelines, checks
guideline consistency as satisfiability, and uses an active tuberculosis diagnosis guideline
as the case study. "Decidable" is in the verified title. Treat everything beyond the title as
unverified until the chapter is read.

### guo2016 — Guo et al. (2016)
**PMID:** none | **DOI:** 10.1109/iccps.2016.7479121 | **Access:** paywalled. *Full text requires institutional access.*
Abstract source: OpenAlex (reconstructed from inverted index).

**Abstract:**
> Improving effectiveness and safety of patient care is an ultimate objective for medical cyber- physical systems. However, the existing medical best practice guidelines in hospital handbooks are often lengthy and difficult for medical staff to remember and apply clinically. Statechart is a widely used model in designing complex systems and enables rapid prototyping and clinical validation with medical doctors. However, clinical validation is often not adequate for guaranteeing the correctness and safety of medical cyber-physical systems, and formal verification is required. The paper presents an approach that transforms medical best practice guidelines to verifiable statechart models and supports both clinical validation in collaboration with medical doctors and formal verification. In particular, we use an open source statechart tool Yakindu to model best practice guidelines and use the statechart to interact with doctors for validating the model correctness. The statechart model is then automatically transformed to a verifiable formal model, such as timed automata, so that existing formal verification tool, such as UPPAAL, can be used to verify required safety properties. The approach also provides the ability to trace back to the paths in the statechart model (Yakindu model) when a specific property in its associated formal model (UPPAAL model) fails. A cardiac arrest scenario is used as a case study to validate the proposed approach. The tool is available on our website www.cs.iit.edu/~code/software/Y2U.

**Key findings (abstract only):** Best-practice guidelines are modeled as Yakindu statecharts,
validated with clinicians, then transformed to timed automata and checked for safety properties
in UPPAAL, with counterexamples traced back to the statechart. The case study is cardiac
arrest. This gives clock-time deadlines and tool support, but for procedural protocols, not for
sets of independent obligations.

### mulyar2008 — Mulyar, Pesic, van der Aalst, Peleg (2008)
**PMID:** none | **DOI:** 10.1007/978-3-540-78238-4_35 | **Access:** paywalled. *Full text requires institutional access.*
Abstract source: University of Haifa research portal (verbatim).

**Abstract:**
> Recent analysis of clinical Computer-Interpretable Guideline (CIG) modelling languages from the perspective of the control-flow patterns has revealed limited capabilities of these languages to provide flexibility for encoding and executing clinical guidelines. The concept of flexibility is of major importance in the medical-care domain since no guarantee can be given on predicting the state of patients at the point of care. In this paper, we illustrate how the flexibility of CIG modelling languages can be improved by describing clinical guidelines using a declarative approach. We propose a CIGDec language for modelling and enacting clinical guidelines.

**Key findings (abstract only):** CIGDec brings the Declare approach (constraints such as
response, precedence and not-coexistence, with LTL semantics over finite executions) to
guidelines. The LTL grounding is my background knowledge of Declare; the abstract says only
"declarative approach". It is motivated by flexibility, not by conflict detection.

### governatori2007 — Governatori, Hulstijn, Riveret, Rotolo (2007)
**PMID:** none | **DOI:** 10.1007/978-3-540-76928-6_50 | **Access:** green OA (submitted version, VU Amsterdam repository, hdl 1871/11495). **PDF:** tried, failed: `research.vu.nl/files/73709883/fulltext` returned 403 Cloudflare.
Abstract source: VU Amsterdam research portal (verbatim).

**Abstract:**
> We provide a conceptual analysis of several kinds of deadlines, represented in Temporal Modal Defeasible Logic. The paper presents a typology of deadlines, based on the following parameters: deontic operator, maintenance or achievement, presence or absence of sanctions, and persistence after the deadline. The deadline types are illustrated by a set of examples.

**Key findings (abstract only):** Its four parameters (deontic operator; achievement vs
maintenance; sanction; persistence after the deadline) are a ready-made schema for extracted
timed obligations: "within 7 days" is an achievement deadline, "for 12 weeks" is a
maintenance obligation, and a sanction is a contrary-to-duty hook. The paper does not
discuss guidelines.

### broersen2004 — Broersen, Dignum, Dignum, Meyer (2004)
**PMID:** none | **DOI:** 10.1007/978-3-540-25927-5_5 | **Access:** green OA (Utrecht repository, hdl 1874/11502).
**PDF:** **saved** at `references/pdfs/broersen2004.pdf` (from dspace.library.uu.nl; `%PDF` magic and `application/pdf` checked).
Abstract source: the saved PDF (verbatim).

**Abstract:**
> This paper studies the logic of a dyadic modal operator for being obliged to meet a condition ρ before a condition δ becomes true. Starting from basic intuitions we arrive at a simple semantics for deadline obligations in terms of branching time models. We show that this notion of deadline obligation can be characterized in the branching time logic CTL. The defined operator obeys intuitive logic properties, like monotony w.r.t. ρ and anti-monotony w.r.t. δ, and avoids some counterintuitive properties like agglomeration w.r.t ρ and 'weak agglomeration' w.r.t. δ. However, obligations of this type are implied by the actual achievement of ρ before the deadline. We argue that this problem is caused by the fact that we model the obligation only from the point of view of its violation conditions. We show that the property might be eliminated by considering success conditions also.

**Key findings (from full text):** The deadline obligation O(ρ ≤ δ) is defined by its
violation condition and reduced to a CTL formula using the Until operator. The authors choose
CTL deliberately, citing P-complete CTL model checking against PSPACE-complete LTL. The
deadline δ is a *condition*, not a clock value, so "within 7 days" needs δ to be a clock
proposition supplied from outside. Branching-time models are the frame class STIT is built on
(Broersen later wrote the deontic epistemic STIT work that gamen-hs's XSTIT follows), so this
is the closest bridge from G3DS to deadlines.

### zamborlini2017 — Zamborlini et al. (2017)
**PMID:** 28410780 | **DOI:** 10.1016/j.artmed.2017.03.012 | **PMC:** none
**Access:** Unpaywall bronze (ScienceDirect). **PDF:** tried, failed (403 Cloudflare).

**Abstract:**
> Accounting for patients with multiple health conditions is a complex task that requires analysing potential interactions among recommendations meant to address each condition. Although some approaches have been proposed to address this issue, important features still require more investigation, such as (re)usability and scalability. To this end, this paper presents an approach that relies on reusable rules for detecting interactions among recommendations coming from various guidelines. It extends a previously proposed knowledge representation model (TMR) to enhance the detection of interactions and it provides a systematic analysis of relevant interactions in the context of multimorbidity. The approach is evaluated in a case study on rehabilitation of breast cancer patients, developed in collaboration with experts. The results are considered promising to support the experts in this task.

**Key findings (abstract only):** Reusable rules over the TMR knowledge model detect
interactions (such as contradiction or repetition) between recommendations from several
guidelines, evaluated on breast cancer rehabilitation with experts. The abstract does not name
OWL. That TMR is an OWL/RDF model queried with SPARQL-style rules is my recollection,
**unverified here**. The paper is the closest evidence for the description-logic row, and it
is only indirect evidence.

### michalowski2021 — Michalowski, Wilk, Michalowski, Carrier (2021)
**PMID:** 33581823 | **DOI:** 10.1016/j.artmed.2020.102002 | **PMC:** none | **Access:** paywalled. *Full text requires institutional access.*

**Abstract:**
> As the population ages, patients' complexity and the scope of their care is increasing. Over 60% of the population is 65 years of age or older and suffers from multi-morbidity, which is associated with two times as many patient-physician encounters. Yet clinical practice guidelines (CPGs) are developed to treat a single disease. To reconcile these two competing issues, previously we developed a framework for mitigation, i.e., identifying and addressing adverse interactions in multi-morbid patients managed according to multiple CPGs. That framework relies on first-order logic (FOL) to represent CPGs and secondary medical knowledge and FOL theorem proving to establish valid patient management plans. In the work presented here, we leverage our earlier research and simplify the mitigation process by representing it as a planning problem using the Planning Domain Definition Language (PDDL). This new framework, called MitPlan, identifies and addresses adverse interactions using durative planning actions that embody clinical actions (including medication administration and patient testing), supports a physician-defined length of planning horizons, and optimizes plans based on patient preferences and action costs. It supports a variety of criteria when developing management plans, including the total cost of prescribed treatment and the cost of the revisions to be introduced. The solution to MitPlan's planning problem is a sequence of timed actions that are easy to interpret when creating a management plan. We demonstrate MitPlan's capabilities using illustrative and clinical case studies.

**Key findings (abstract only):** The earlier mitigation framework used FOL and theorem
proving. MitPlan recasts it as PDDL planning with *durative* actions, a physician-set planning
horizon, and cost/preference optimization, producing a sequence of timed actions. The key
point for us: the group itself moved from FOL to planning to get time and revision into the
same formalism. Detection plus *repair* is their contribution; ours is detection.

### piovesan2020 — Piovesan, Terenziani, Theseider Dupré (2020)
**PMID:** 32001389 | **DOI:** 10.1016/j.jbi.2020.103377 | **PMC:** none
**Access:** Unpaywall bronze (ScienceDirect). **PDF:** tried, failed (403 Cloudflare).

**Abstract:**
> The treatment of comorbid patients is a hot problem in Medical Informatics, since the plain application of multiple Computer-Interpretable Guidelines (CIGs) can lead to interactions that are potentially dangerous for the patients. The specialized literature has mostly focused on the "a priori" or "execution-time" analysis of the interactions between multiple Computer-Interpretable Guidelines (CIGs), and/or CIG "merge". In this paper, we face a complementary problem, namely, the a posteriori analysis of the treatment of comorbid patients. Given the CIGs, the history of the status of the patient, and the log of the clinical actions executed on her, we try to explain the actions executed on the patient (i.e., the log) in terms of the actions recommended by the CIGs, of their potential interactions, and of the possible ways of managing each such interaction, pointing out (i) deviations from CIG recommendations not explained in terms of interaction management (if any) and (ii) unmanaged interactions (if any). Our approach is based on Answer Set Programming, and, to face realistic problems, devotes specific attention to the temporal dimension.

**Key findings (abstract only):** ASP explains a comorbid patient's action log by the
recommendations of several CIGs, their interactions and the ways of managing them, reporting
unexplained deviations and unmanaged interactions. It gives "specific attention to the
temporal dimension". Deviation-from-recommendation is a violation notion, which makes this the
nearest ASP analogue to deontic conformance.

---

## Part 4 — Comparison matrix

Legend: **yes / partial / no**, a one-line reason, and the supporting key. "No source found"
means no paper in this set supports the cell; the entry then is my own judgment and is marked
*(judgment)*.

| Candidate logic | (a) Temporal: deadlines, periodicity, sequencing | (b) Deontic force: O/P/F, CTD, deadline obligations | (c) Missing / unknown patient data | (d) Decidability and tool support | (e) Fit with CIG formalisms |
|---|---|---|---|---|---|
| **LTL / LTLf, Declare constraints** | **partial.** Qualitative sequencing (before/after/until, eventually), no clock time or periodicity; `mulyar2008` for Declare-on-guidelines; the clock-time limit is no source found *(judgment)* | **no.** Constraints are implicitly mandatory, with no permission, prohibition-vs-obligation distinction or CTD. No source found *(judgment)* | **partial.** The motivation is flexibility because patient state is unpredictable at the point of care (`mulyar2008`); no explicit unknown-value semantics | **yes.** LTLf satisfiability is decidable, with automata-based tools. No source found in this set (De Giacomo & Vardi 2013 not verified) | **partial.** CIGDec (`mulyar2008`) is a guideline language, but a workshop-level proposal |
| **Metric temporal logic, timed automata, UPPAAL** | **yes.** Clock deadlines and durations through timed automata (`guo2016`); metric intervals (`sanati2014`, title and summary only) | **no.** Safety properties over protocol states, no deontic operators (`guo2016`) | **no.** No source found; nondeterministic inputs could model unknowns *(judgment)* | **yes.** UPPAAL checks timed automata automatically (`guo2016`); decidable metric interval logic (`sanati2014`, title) | **partial.** Statecharts of hospital protocols, not CIG languages (`guo2016`); a TB guideline case study (`sanati2014`, unverified summary) |
| **Interval / temporal-constraint reasoning (GLARE, STP-style; Allen)** | **yes.** Durations, delays, composite and periodic repeated actions (`anselma2006`) | **no.** Constraints on action times only. No source found *(judgment)* | **partial.** Checks execution times against constraints, so it tolerates partially known timelines (`anselma2006`); no explicit unknown-data treatment | **yes.** "Correct, complete and tractable" propagation (`anselma2006`) | **yes.** Built into GLARE (`anselma2006`, `bottrighi2010`) |
| **Temporal deontic logic with deadlines (Governatori; Broersen)** | **partial.** Deadlines as conditions, achievement vs maintenance, persistence (`governatori2007`, `broersen2004`); no clock arithmetic or periodicity (`broersen2004`: δ is a condition) | **yes.** Deontic operator, sanctions, violation conditions (`governatori2007`, `broersen2004`); CTD via sanctions (`governatori2007`) | **partial.** Defeasibility tolerates incomplete rule sets, but that is not unknown patient data. No source found *(judgment)* | **partial.** Reducible to CTL, P-complete model checking (`broersen2004`); tool support for defeasible deontic logic, no source found | **no.** No guideline application found. No source found |
| **Description logics (OWL, SNOMED CT)** | **no.** No source found; OWL has no native time *(judgment)* | **partial.** Recommendations carry a polarity (do/avoid), per TMR (`zamborlini2017`, recollection beyond the abstract) | **partial.** The open-world assumption treats absent facts as unknown. No source found *(judgment)* | **yes.** Decidable DL reasoners. No source found in this set *(judgment)* | **yes.** Interaction detection across multiple guidelines (`zamborlini2017`) |
| **Model checking of CIGs (Asbru/GLARE/PROforma/GLIF; SPIN, NuSMV, KIV)** | **partial.** LTL path properties via SPIN (`bottrighi2010`); task execution over time in Asbru networks (`hommersom2007`) | **no.** Checks guideline paths and quality criteria, not obligations (`bottrighi2010`, `hommersom2007`) | **partial.** Adds medical background knowledge to guideline models (`hommersom2007`) | **yes / partial.** SPIN is fully automatic (`bottrighi2010`); KIV is an interactive prover (`hommersom2007`) | **yes.** GLARE (`bottrighi2010`), Asbru task networks (`hommersom2007`) |
| **FOL / planning for multimorbidity mitigation (Wilk & Michalowski)** | **partial.** Durative actions and a planning horizon (`michalowski2021`); periodicity no source found | **partial.** Adverse interactions and revisions, with no deontic modalities (`michalowski2021`) | **partial.** Secondary medical knowledge fills gaps (`michalowski2021`); no explicit unknown semantics | **partial.** FOL is undecidable in general; PDDL planners are automatic (`michalowski2021`) | **yes.** Designed for concurrent CPGs (`michalowski2021`) |
| **Answer set programming** | **partial.** Temporal dimension handled explicitly (`piovesan2020`); metric and periodic detail not in the abstract | **partial.** Deviation from recommendation is a violation notion (`piovesan2020`); no P/F/CTD operators | **partial.** Default negation suits incomplete data. No source found *(judgment)* | **yes.** Automatic ASP solvers (`piovesan2020`) | **yes.** Multiple CIGs, comorbid patients (`piovesan2020`) |
| **Current stack: deontic STIT (G3DS) + KD tableaux** (for reference) | **no.** Temporal layer quarantined (project state) | **yes.** Obligation, permission and prohibition with agency (project state) | **no.** Project state | **yes.** Tableau prover in gamen-hs (project state) | **partial.** Works on extracted obligation sets, not CIG models (project state) |

Reviews supporting the framing: `peleg2013` (V&V and temporal expressions as CIG themes),
`bilici2018` (conflict detection and temporal constraints listed as separate approaches in
multimorbidity CDSS).

### Recommendation

**What the papers say.**
- Periodic and duration constraints in guidelines can be checked for consistency by constraint
  propagation that is correct, complete and tractable (`anselma2006`).
- Deadline obligations have a clean semantics in branching time and reduce to CTL
  (`broersen2004`). A typology of deadlines (achievement vs maintenance, sanctions,
  persistence) exists for extracted norms to be classified against (`governatori2007`).
- Model checking and timed automata find real inconsistencies in guidelines, but they model
  procedures, not obligations (`bottrighi2010`, `guo2016`).
- The multimorbidity groups, whose problem is closest to ours, moved to formalisms that carry
  time natively: ASP (`piovesan2020`) and durative planning (`michalowski2021`).
- No paper in the set combines metric or periodic time with deontic force and applies it to
  guidelines.

**My judgment.** Keep G3DS/KD as the deontic core, and add two decidable layers rather than
adopting one monolithic logic.

1. **A temporal-constraint layer in the GLARE/STP style.** Represent each timed obligation's
   window ("within 7 days", "for 12 weeks", "every 3 months") as bounds on action times and
   repetitions, and check joint satisfiability by constraint propagation. For simple temporal
   networks this is negative-cycle detection, which is small, total and provable in Lean.
2. **A Broersen-style deadline operator O(ρ ≤ δ).** Add it to the branching-time frame the
   STIT layer already uses, with δ grounded by the constraint layer, and classify each
   extracted timing field with Governatori's typology (achievement vs maintenance).

Conflict detection then reads: the deontic layer flags obligation pairs that are co-applicable
and opposed (or jointly unrealizable), and the temporal layer decides whether their windows
actually overlap. This avoids a quarantined qualitative tense logic, keeps decidability, and
covers the "periodic / eventually / always" 14% without MTL or UPPAAL. Those are better suited
to protocol-level verification than to sets of extracted obligations.

Periodic constraints beyond simple repetition will need Anselma's restricted forms. That
tractability trade-off should be read in the full text before committing.

**Requirement no candidate covers well: (c) missing or unknown patient data.** No paper in the
set gives it a formal semantics. The partial marks rest on side effects (OWL's open world,
ASP's default negation, background knowledge). A three-valued or "unknown-applicability"
treatment of obligation antecedents would be new work. The combination of (a) clock or
periodic time with (b) CTD in a decidable, guideline-applied system is also unoccupied in
this set.
