.. _groups_and_ring:


群与环
================

我们已经在 :numref:`proving_identities_in_algebraic_structures` 中学习过如何对群与环中的运算进行推理，并在稍后的 :numref:`section_algebraic_structures`中领略了定义抽象代数结构的方法。这类结构诸如群，
或是像高斯整环这样的具体例子。 :numref:`Chapter %s <hierarchies>` 中解释了 Mathlib 如何处理抽象结构的层级关系。

本章中，我们将更为详细地探讨群和环。由于 Mathlib 总在扩展中，我们没办法涵盖 Mathlib 中有关这一主题的所有方面。
但我们将为你给出使用相关库的切入点，并展示如何使用其中的核心概念。
这一章和
:numref:`Chapter %s <hierarchies>` 有些重复，但在这儿我们会集中于使用 Mathlib，而非探究其背后的设计理念。
因此，要理解本章中的一些例子，你可能需要回顾
:numref:`Chapter %s <hierarchies>`。
