from pathlib import Path
import re

from pathlib import Path
import re


def process_latex_content(latex_content):
    """
    Processes the LaTeX content to replace \dfn, \prop, and \cor commands, using a stack to efficiently handle nested curly brackets
    and dropping empty optional arguments.
    """
    # Mapping of commands to their corresponding LaTeX environment names
    command_to_env = {
        '\\dfn': 'definition',
        '\\prop': 'proposition',
        '\\cor': 'corollary',
        '\\lemm': 'lemma',
        '\\thm': 'theorem',
        '\\ex': 'example',
        '\\pf': 'prf',
    }

    stack = []  # Stack to keep track of the positions of opening curly brackets
    output = []  # Output list to build the processed content
    i = 0  # Current position in the input content

    while i < len(latex_content):
        char = latex_content[i]

        if char == '\\':  # Escape sequence (e.g., LaTeX command)
            # Find the end of the command (space or a curly bracket)
            end_pos = i + 1
            # if char is the last character, or the next character is not a letter, then break
            if end_pos >= len(latex_content) or not latex_content[end_pos].isalpha():
                cmd = 'not a command'
            else:
                while end_pos < len(latex_content) and latex_content[end_pos] not in (' ', '{', '[', '\\'):
                    end_pos += 1
                cmd = latex_content[i:end_pos]  # Extracted command

            if cmd in command_to_env:
                # Process the recognized command
                env_name = command_to_env[cmd]  # Get the corresponding environment name
                i = end_pos  # Move past the command

                opt_arg = ""  # Optional argument (e.g., the label)
                if i < len(latex_content) and latex_content[i] == '[':
                    opt_arg_start = i
                    i = latex_content.find(']', i) + 1
                    if i == 0:  # No closing ']' found or it's the last character
                        break
                    opt_arg = latex_content[opt_arg_start + 1:i - 1]

                # Now, handle the curly brackets with the stack
                args = []  # List to keep the extracted arguments

                max_arg_count = 1 if cmd == '\\pf' else 2  # number of arguments
                while i < len(latex_content) and len(args) < max_arg_count:  # Ensure i is in bounds
                    current_char = latex_content[i]
                    # Check for math environments and skip them, because they can contain unpaired '{'
                    if latex_content[i:i + 1] == '$':  # Single dollar math environment
                        end_pos = latex_content.find('$', i + 1) + 1
                    elif latex_content[i:i + 2] == '$$':  # Double dollar math environment
                        end_pos = latex_content.find('$$', i + 2) + 2
                    elif latex_content[i:i + 2] == '\\[':  # Display math environment
                        end_pos = latex_content.find('\\]', i + 2) + 2
                    elif latex_content[i:i + 14] == r'\begin{align*}':  # Generic \begin \end block
                        end_pos = latex_content.find(r'\end{align*}', i + 14) + 12
                    elif latex_content[i:i + 14] == r'\begin{tikzcd}':
                        end_pos = latex_content.find(r'\end{tikzcd}', i + 14) + 12
                    elif latex_content[i:i + 17] == r'\begin{equation*}':
                        end_pos = latex_content.find(r'\end{equation*}', i + 17) + 15

                    if end_pos > i:
                        i = end_pos  # Skip the entire math environment or \begin \end block
                        continue

                    if current_char == '{':
                        stack.append(i)
                    elif current_char == '}' and stack:
                        start = stack.pop()
                        if not stack:  # If the stack is empty, we've found an outermost argument
                            args.append(latex_content[start + 1:i])
                    i += 1

                if max_arg_count == 1 and len(args) == 1:
                    # For the \pf command, we don't need to handle the last argument
                    replacement = f"\\begin{{{env_name}}}{args[0]}\\end{{{env_name}}}\n"
                    output.append(replacement)
                elif len(args) >= 2:
                    # Construct the replacement string, checking for an empty optional argument
                    # opt_arg = f"{{{opt_arg}}}" if opt_arg else ""
                    content = args[1] if len(args) == 2 else ""
                    replacement = f"\\begin{{{env_name}}}{{{args[0]}}}{{{opt_arg}}}{content}\\end{{{env_name}}}\n"
                    output.append(replacement)
                continue  # Skip the rest of the loop and continue processing
            else:
                # Not one of the recognized commands, just copy the command to the output
                output.append(latex_content[i:end_pos])
                i = end_pos
                continue

        # If not part of a command, or not handling brackets, just add the character to the output
        if not stack and i < len(latex_content):
            output.append(char)
        i += 1

    return ''.join(output)


def expand_dfn_macro(input_tex_path):
    input_path = Path(input_tex_path)
    output_path = 'macro_expanded' / input_path.with_stem(f"{input_path.stem}")
    # create the output directory if it doesn't exist with pathlib
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(input_tex_path, 'r', encoding='utf-8') as file:
        content = file.read()
    processed_content = process_latex_content(content)
    with open(output_path, 'w', encoding='utf-8') as file:
        file.write(processed_content)
    return output_path


test_input = r'''
\[
    \overline{a_1\cdots a_n}\diamond \overline{b_1\cdots b_m}=\overline{a_1\cdots a_nb_1\cdots b_m}.
\]
\dfn{Word}{
    Let $S$ be a set. Define $S^{-1}=\left\{s^{-1}\midv s\in S\right\}$. A \textbf{word} on $S$ is a string over $S\sqcup S^{-1}\sqcup\{1\}$. $\overline{1}$ is called an \textbf{empty word}. The \textbf{length} of a word $w$ is the number of letters in $w$.
}
Associatedness can also be described in terms of the action of $R^\times$ on $R$ via multiplication: two elements of $R$ are associates if they are in the same $R^\times$-orbit.
\dfn{Irreducible Element}{
    Let $R$ be an integal domain. An element $a\in R$ is called \textbf{irreducible} if
    \begin{enumerate}[(i)]
        \item $a\notin R^\times$, i.e. $a$ is not a unit.
        \item $a=bc\implies b\in R^\times\text{ or }c\in R^\times$.
    \end{enumerate}    
}
\[
\left\{\text{maximal ideals of }R\right\} \subseteq \left\{\text{prime ideals of }R\right\} \subseteq \left\{\text{radical ideals of }R\right\} \subseteq \left\{\text{ideals of }R\right\}.
\]
\prop{Quotient Preserves Radical, Prime, Maximal Ideals}{
    Let $R$ be a commutative ring and $I\subseteq R$ be a proper ideal. Then we have bijections between the following sets:
    \begin{align*}
        \left\{\text{ideals of }R\text{ containing }I\right\}&\longleftrightarrow\left\{\text{ideals of }R/I\right\}\\
        J&\longmapsto J/I
    \end{align*}
    The ideal $J\supseteq I$ is radical, prime, or maximal if and only if $J/I$ is radical, prime, or maximal respectively.
}
\[
    \mathsf{Ring}
\]
\dfn{Unit Group of a Ring}{
    Let $R$ be a ring. The \textbf{unit group} of $R$ is the group of invertible elements of $R$ under multiplication, denoted by $R^\times$. We can define a functor $(-)^\times:\mathsf{Ring}\to\mathsf{Grp}$ that sends a ring to its unit group
    \[
        \begin{tikzcd}[ampersand replacement=\&]
            \mathsf{Ring}\ \&[-25pt]\&[+10pt]\&[-30pt]\mathsf{Grp}\&[-30pt]\&[-30pt] \\ [-15pt] 
            R \arrow[dd, "f"{name=L, left}] 
            \&[-25pt] \& [+10pt] 
            \& [-30pt]R^{\times}\arrow[dd, "f|_{R^\times}"{name=R}] \\ [-10pt] 
            \&  \phantom{.}\arrow[r, "(-)^\times", squigarrow]\&\phantom{.}  \&   \\[-10pt] 
            S  \& \& \& S^{\times}
        \end{tikzcd}
    \]
}

\prop{Adjunction $\mathbb{Z}\left[-\right]\dashv \left(-\right)^\times$}{
    $(-)^\times:\mathsf{Ring}\to\mathsf{Grp}$ has a left adjoint which sends each group $G$ to the group ring $\mathbb{Z}\left[G\right]$.
}


'''

print(process_latex_content(test_input))


filename_list = [
    'set_theory.tex',
    'category_theory.tex',
    'group.tex',
    # 'topological_group.tex',
    #'ring.tex',
    'commutative_ring.tex',
    'module.tex',
    # 'associative_algebra.tex',
    # 'field.tex',
    # 'valuation_theory.tex',
    # 'number_theory.tex',
]

for input_tex_path in filename_list:
    expand_dfn_macro(input_tex_path)

