<h1 align="center"> $\mathrm{QuantSem}$ </h1>

<div id="toc" align="center">
<ul style="list-style: none">
<summary>
<h1> 
$\bigotimes\mathcal{H}^\dagger\bigoplus \quad \Huge{\color{#C022E0}\langle \space\text{Qu}\color{#9638D6}\text{an}\color{#7449CE}\text{tum}  \space \color{#4D6CCA}\mid \space\color{#4085CD}\text{Le} \color{#30A3D1}\text{an} \space \color{#30A3D1}\rangle} \quad \lambda.\Pi\Sigma$
</h1>
</br>
<h2> A High-level Lean formalization of Quantum Computing </h2>
</summary>
</ul>
</div>

<!-- ![Static Badge](https://img.shields.io/badge/mathlib-depends?style=for-the-badge&label=Depends%20on&color=blue&link=href%3D%22https%3A%2F%2Fgithub.com%2Fleanprover-community%2Fmathlib4%2Freleases%2Ftag%2Fv4.31.0%22) -->




## 👁️‍🗨️ Overview

<div align="center">
  
$\mathrm{QuantSem}$ is a Lean formalization of Quantum Computing aimed at conciling general high-level Quantum Computing syntax and it's underlying mathematical semantics, while providing a self-contained language for Quantum Computing.

</div>
</br>

## 📊 Status of the project

* At the moment, a crude categorical description of general quantum computing has been established. This allows to talk about Quantum states, Quantum gates and Quantum Circuits without worrying about the mathematical reality.

* A refinement of this category for Hilbert spaces with a basis is also implemented, allowing a concrete description of states and gates through their effect on a basis.

* Some tools allowing for a coercion of unitary matrices and vectors to the usual Complex-Euclidean spaces allow the user to define concrete states, gates, and use these tools to build Quantum circuits translating computation at a high level while providing the necessary algebra. 

</br>

## 🏆 Current capabilities

$\mathrm{QuantSem}$ provides a ```Test``` folder, in which the .lean files give an idea of the language and it's current expressiveness power.

* ```test.lean``` shows the concrete description of states, gates and circuits as programmed by the user. Some useful tactics for proving unitarity allow the user to not worry about their implementation as long as the data is indeed unitary in the usual Euclidean spaces.

</br>

## TODO : 
* Refine the Category of Hilbert spaces with a basis to be a dependent product allowing to carry the data of the basis (for now, it is the full subcategory produced by the property "there exists a basis", the axiom of choice comes back to bite us later) [ ❌ ]
  _one could also think of refining the non-dependent product with the property that the second element of the tuple forms a basis of the first element_
* Modify BasisCircuit's RegisterSwap to take BasisReg iso's rather than QuantReg iso's [ ❌ ]
* Complete the fact that a tensor register is the span of it's separable elements (the equivalence has been written, need to write the induction theorem to reflect the one on spans) [ ⏳ ]
* Find the syntax for Controlled Gates [ ⏳ ]
