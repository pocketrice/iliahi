
$\newcommand{\comm}[1]{\;\text{#1}\;}$
$\newcommand{\zq}{\phantom{}^2}$

**1.**
*(a)* 
If $m$ and $n$ are odd and even integers respectively, then $m+n$ is odd.

*(b)*
If $m$ is an even integer, then $m+1$ is an odd integer.

**2.**
Since $m$ is odd there exists an integer $k$ such that $m=2k+1$.
Since $n$ is odd there exists an integer $l$ such that $n=2l+1$.

$m+n=(2k+1)+(2l+1)$
$\qqq=2(k+l+1)$

Let $j=k+l+1$. As the sum of integers is still an integer, $j$ is thus an integer.

As $m+n=2j$, by definition $m+n$ is even.

**3.**
*(a)*
Assume for some integer $m$ that it is odd; this must mean there exists an integer $l$ such that $m=2l+1$. 

By definition $m^2=m\cdot m$, meaning $m^2=m\cdot m=(2l+1)(2l+1)=4l^2+4l+1$. 

Let $j=2l^2+2l$. As multiplying or adding an integer by an integer results in an integer, $j$ thus must be an integer.

Since $m^2=2j+1$, $m^2$ is odd. This means $m$ being odd is sufficient for $m^2$ to be odd.

As a sentence is logically equivalent to its contrapositive, this means for any integer $m$, $m^2$ being even is sufficient for $m$ to be even. $\qed$

*(b)*
Assume for some integer $m$ that it is even; this must mean there exists an integer $l$ such that $m=2l$.

By definition $m^2=m\cdot m$, meaning $m^2=m\cdot m=(2l)(2l)=4l^2$.

Let $j=2l$. As multiplying any integer by itself results in an integer, $j$ thus must be an integer.

Since $m^2=2j$, $m^2$ is even. This means $m$ being even is sufficient for $m^2$ to be even.

As a sentence is logically equivalent to its contrapositive, this means for any integer $m$, $m^2$ being odd is sufficient for $m$ to be odd. $\qed$

**4.**
The statement may be rewritten as $(\forall n \in \mathbb{R})(n^2\comm{divisible by 4}\implies n\comm{divisible by 4})$.

The negation of a conditional of the form $P\implies Q$ is $P\land \neg Q$, meaning the negation of the statement is "$n^2\;\text{divisible by 4}\land n\;\text{not divisible by 4}$".

Consider 10, which makes said negation true (as $10^2=100$ is divisible by 4 and $10$ is not divisible by 4).

As making the negation of a statement true is logically equivalent to the statement itself being false, this statement must be false because $n=10$ is an element of $\mathbb{R}$ that makes the negation true.

**5.**
*(a)*
Assume $n_{1},n_{2}$ are squares; this means there exists integers $m_{1},m_{2}$ such that $n_{1}=m_{1}\zq$ and $n_{2}=m_{2}\zq$.

This means $n_{1}n_{2}=m_{1}\zq m_{2}\zq$.

By definition $m_{1}\zq m_{2}\zq=m_{1}m_{1}m_{2}m_{2}=(m_{1}m_{2})^2$.

Thus if $n_{1},n_{2}$ are squares then $n_{1}n_{2}$ is also a square. $\qed$

*(b)*
For any integers $n_{1},n_{2}$, if $n_{1}n_{2}$ is a square then $n_{1}$ and $n_{2}$ are squares.

*(c)*
Consider $n_{1}=5$ and $n_{2}=5$.

$n_{1}n_{2}=25$ is a square but $n_{1}$ and $n_{2}$ themselves are not, thus meaning the converse must be false because $n_{1}=5,n_{2}=5$ are elements of $\mathbb{R}$ where $n_{1}n_{2}$ is a square but $n_{1}$ and $n_{2}$ are not.

