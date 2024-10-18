# Lean 形式化数学

本教程基于 Lean 4，VS Code，和 Mathlib。[英文版](https://leanprover-community.github.io/mathematics_in_lean/)

在您的计算机上使用此存储库的副本。或者，你可以使用Github Codespaces或Gitpod在云上运行 Lean 和 VS Code。

本书介绍 [Lean 4](https://leanprover.github.io/) 和
[Mathlib](https://github.com/leanprover-community/mathlib4).
Lean 3 版 [https://github.com/leanprover-community/mathematics_in_lean3](https://github.com/leanprover-community/mathematics_in_lean3).


# 源文件在master目录下，项目文件在gh-pages目录下

# 源文件readme

This repository is used to generate the textbook and user repository for
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).

Our build process applies rudimentary scripts to marked up Lean files to generate
- source files for the textbook,
- Lean exercise files, and
- Lean solution files,

and put them all in the right places.

We use [Sphinx](https://www.sphinx-doc.org/en/master/)
 and the [Read the Docs theme](https://sphinx-rtd-theme.readthedocs.io/en/stable/) to generate
 the HTML and PDF versions of the textbook.

Finally, we use another script to deploy the contents to the
[user repository](https://github.com/leanprover-community/mathematics_in_lean).


Setup
-----

To edit the Lean files, you need to have Lean, github, and friends installed.
See the instructions on the [Lean community web pages](https://leanprover-community.github.io/) .
In particular, don't forget to use
```
lake exe cache get
```
after fetching this repository to get the compiled version of Mathlib.

To build the textbook, you need to have
[Sphinx and ReadTheDocs](https://sphinx-rtd-tutorial.readthedocs.io/en/latest/install.html)
installed, as well as the Python `regex` package.
Ideally, `pip install -r scripts/requirements.txt` should suffice.


Overview
--------

The Lean source files are in the `MIL` directory. There is a folder for each chapter, the
name of which begins with the letter `C` and the chapter number.
The scripts sort the chapters and ignore folders that do not begin with `C`.

Each folder should contain an `.rst` file with the same name, which has the chapter header
for Sphinx. Each folder also has a Lean source file for each section,
the name of which begins with `S` and the section number.
The scripts ignore Lean files that do not begin with `S`.
The markup that is used to generate the content is described below.

The folder `sphinx_source` contains files that are automatically added to a generated folder
called `source`, which is used by Sphinx.
It includes, in particular, a folder for any figures you want to use in the textbook.

The folder `user_repo_source` contains files that are automatically added to a generated
folder called `user_repo`, which is used to build the user repository.
It includes, in particular, the `README` file for that repository.


Build
-----

Running `scripts/mkall.py` does the following:
- It creates and initializes a `source` directory, for use by Sphinx.
- It creates and initializes a `user_repo` directory with files that will be
  deployed to the user repository.
- It updates the file `MIL.lean` to match the contents of the `MIL` folder.

With the `source` directory in place, you can use `make html` and `make latexpdf` to
call Sphinx to build the HTML and PDF versions of the book, respectively.
Sphinx puts these in a generated `build` directory.

Running `scripts/deploy.sh leanprover-community mathematics_in_lean` calls all three of the
previous scripts, copies the HTML and PDF versions of the book to `user_repo`,
and deploys the user repository to the github repository `leanprover-community/mathematics_in_lean`.
You can deploy to another destination for testing.

Running `scripts/clean.py` deletes the `source`, `user_repo`, and `build` directories.


Markup
------

The Lean files in the `MIL` folder generate three types of files:
- Source files for the Sphinx textbook.
- Files with examples (and exercises) for the user repository.
- Files with solutions for the user repository.
A line of text from the Lean file may go to any combination of these destinations simultaneously,
or nowhere at all, as determined by simple markup directives in the file.

When `scripts/mkall.py` starts processing a file,
it sends output to both the associated examples file and the associated solutions file by default.
This makes sense, for example, for the import lines.

The following markup specifies material for the textbook:
```
/- TEXT:
Stuff for the textbook goes here.
TEXT. -/
```
The lines between the comments are sent only to the associated Sphinx source file.

After the line `TEXT. -/`, by default, lines of text are sent only to the
examples file.
You can replace the last line with `EXAMPLES: -/`, which has the same effect,
`SOLUTIONS: -/` to send the lines to the solutions file,
`BOTH: -/` to send the lines to the both files,
or `OMIT: -/` to send the lines to neither.

You can subsequently modify the behavior with the additional comment lines
`-- EXAMPLES:`, `-- SOLUTIONS:`, `-- BOTH:`, and `-- OMIT:`.
The behavior stays in effect until another directive changes it.

While the script is processing lines of Lean code, you can specify that a sequence of lines
should be added to the textbook as a block quote by enclosing it as follows:
```
-- QUOTE:
example : 1 + 1 = 2 := by rfl
-- QUOTE.
```
Note the use of the period to mark the end of the quote.

In such a quote block, any lines that are designated to go only to the solutions file are not
included in the quote. Thus you can only quote lines that are sent to the examples file,
sent to both the examples and solutions files, or omitted from both.
The behavior of the `QUOTE` directives is otherwise independent of the behavior of the
`EXAMPLES`, `SOLUTIONS`, `BOTH`, and `OMIT` directives.
For example, you can switch output from the examples file to both the examples and solutions
file in the middle of a quote.
It doesn't make a difference whether one of the latter directives occurs just before or
just after a `QUOTE` directive.

You can also use `/- EXAMPLES:`, `/- SOLUTIONS:`, `/- BOTH:`, and `/- OMIT:` to put text
in a block comment that is sent to one of the files accordingly.
This provides a handy way to specify a `sorry` in an examples file
that is replaced by a solution in the solution file.
Here's an example of how these are used:
```
/- TEXT:
Here is an example of the way that ``rintro`` is used:
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
As an exercise, try proving the other inclusion:
BOTH: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- QUOTE.

```
The second text block represents a common idiom for presenting exercises:
after the textbook prose, a `theorem` or `example` line is sent to both the examples
and the solutions file.
The examples file contains only a `sorry`, whereas the solutions file contains the full solution.
The solution is checked by Lean in the source file, but it is not included in the quote.

Note also the useful convention that if a blank line is needed in the examples or
solutions file, it is specified *after* the relevant segment, so that the next
time output is enabled no blank line is needed.
So, in the example above, there is no blank line before or after `-- QUOTE:`
because we assume that prior input has already inserted a blank line,
but there is a blank line after `-- QUOTE.`

It is common to use sections to declare and scope variables in the examples and solutions
files, but to omit the section commands from quote.
Thus you might use the following pattern:
```
/- TEXT:
Here is an example of the way that ``rintro`` is used:
BOTH: -/
section
variable (s t u : Set α)

-- EXAMPLES:
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

```
Just make sure that, later in the file, the matching `end` and a blank line after are sent to
both outputs.

The weird pair of characters `αα` in a Lean input file is simply deleted from any
output produced by the script.
This is a little hack that allows you to produce the same identifier in the examples
and solutions files. For example, the exercise above could have been written
as follows:
```
/- TEXT:
As an exercise, try proving the other inclusion:
EXAMPLES: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem fooαα : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu

```
The theorem is named `foo` in both the examples and the solutions, but Lean doesn't
complain about a duplicate identifier in the source file.

Finally, there is a mechanism that allows you to quote any part of the file
in the textbook, before or after it appears in the Lean source file.
This can be used, for example, to present a long proof and then refer back to parts of it.
Encode the lines you want to quote with a pair of tags:
```
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
-- TAG: my_tag
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- TAG: end
```
The first tag can have any label you want in place of `my_tag`, whereas the second should
be exactly as shown. Adding the line
```
-- LITERALINCLUDE: my_tag
```
in the middle of a text block anywhere in the file will insert the tagged text as a
block quote in the textbook,
using a Sphinx directive that is designed for exactly that purpose.


Testing
-------

After running `scripts/mkall.py`, you can use `lake build` to compile all the lean source files.
This will print all the output generated by `#check`, `#eval`, and other commands found in the
source files, as well as a warning for each `sorry`, and so on. Scanning the output provides
a way to detect whether all the definitions, theorems, and proofs are well formed.
This does not, however, confirm that the examples files and solutions files that are generated
from the lean source files are well formed.

To test the examples, use `scripts/examples_test.py`.
This compiles all the lean source files as with `scripts/mkall.py`,
but then it copies the Lean files from `user_repo` into a folder `MIL/Test` and
constructs `MIL.lean` to import each of those.
Use `lake build` to compile them.

Similarly, use `scripts/solutions_test.py` followed by `lake build` to test all the solutions files.

Use `scripts/clean_test.py` to remove the directory `MIL/Test` and restore `MIL.lean` to import the
Lean source files.


Processing one section
----------------------

Instead of building everything, you can test build a single section with `scripts/mksection.py`.
For example,
```
  scripts/mksection.py C03_Logic S02_The_Existential_Quantifier
```
creates the examples file, the solutions file, and the Sphinx restructured text file
for the section indicated.


How to contribute
-----------------

The textbook is still a work in progress, but feedback and corrections are welcome.
You can open a pull request,
find us on the [Lean Zulip channel](https://leanprover.zulipchat.com/),
or contact us by email.

# 项目文件readme

## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following
   these [instructions](https://leanprover-community.github.io/get_started.html).

2. Make sure you have [git](https://git-scm.com/) installed.

3. Follow these [instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project)
   to fetch the `mathematics_in_lean` repository and open it up in VS Code.

4. Each section in the textbook has an associated Lean file with examples and exercises.
   You can find them in the folder `MIL`, organized by chapter.
   We strongly recommend making a copy of that folder and experimenting and doing the
   exercises in that copy.
   This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below).
   You can call the copy `my_files` or whatever you want and use it to create
   your own Lean files as well.

At that point, you can open the textbook in a web browser
at [https://leanprover-community.github.io/mathematics_in_lean/](https://leanprover-community.github.io/mathematics_in_lean/)
and start reading and doing the exercises in VS Code.

The textbook and this repository are still a work in progress.
You can update the repository by typing `git pull`
followed by `lake exe cache get` inside the `mathematics_in_lean` folder.
(This assumes that you have not changed the contents of the `MIL` folder,
which is why we suggested making a copy.)


## To use this repository with Github Codespaces

If you have trouble installing Lean, you can use Lean directly in your browser using Github
Codespaces.
This requires a Github account. If you are signed in to Github, click here:

<a href='https://codespaces.new/leanprover-community/mathematics_in_lean' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

Make sure the Machine type is `4-core`, and then press `Create codespace`
(this might take a few minutes).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.

Opening any `.lean` file in the MIL folder will start Lean,
though this may also take a little while.
We suggest making a copy of the `MIL` directory, as described
in the instructions above for using MIL on your computer.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Codespaces offers a certain number of free hours per month. When you are done working,
press `Ctrl/Cmd+Shift+P` on your keyboard, start typing `stop current codespace`, and then
select `Codespaces: Stop Current Codespace` from the list of options.
If you forget, don't worry: the virtual machine will stop itself after a certain
amount of time of inactivity.

To restart a previous workspace, visit <https://github.com/codespaces>.


## To use this repository with Gitpod

Gitpod is an alternative to Github Codespaces, but is a little less convenient,
since it requires you to verify your phone number.
If you have a Gitpod account or are willing to sign up for one,
point your browser to
[https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean](https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
We suggest making a copy of the `MIL` directory, as described
in the instructions above for using MIL on your computer.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
If you change the filter from Active to All, you will see all your recent workspaces.
You can pin a workspace to keep it on the list of active ones.


## 如何参与

欢迎 PR，见置顶 issue。
