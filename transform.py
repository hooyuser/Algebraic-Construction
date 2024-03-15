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
            while end_pos < len(latex_content) and latex_content[end_pos] not in {' ', '{', '['}:
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

\thm[yoneda_lemma]{Yoneda Lemma}{
    Let $\mathsf{C}$ be a locally small category. For any functor $F:\mathsf{C}^{\mathrm{op}}\to \mathsf{Set}$ and any $A\in \mathrm{Ob}(\mathsf{C})$, there is a natural bijection
    \begin{align*}
        q_{A,F}:\operatorname{Hom}_{\mathsf{Psh}(\mathsf{C})}\left(\operatorname{Hom}_{\mathsf{C}}\left(-,A\right), F\right) & \overset{\sim}{\longrightarrow} F(A) \\
        {  \left[ \begin{tikzcd}[ampersand replacement=\&]
            \mathsf{C}^{\mathrm{op}} \arrow[r, "\operatorname{Hom}_{\mathsf{C}}\left(-{,}A\right)"{name=A, above}, bend left] \arrow[r, "F"'{name=B, below}, bend right] \&[+30pt] \mathsf{Set}
            \arrow[Rightarrow, shorten <=5.5pt, shorten >=5.5pt, from=A.south-|B, to=B, "\phi"]
        \end{tikzcd}\right] } & \longmapsto \phi_A\left(\operatorname{id}_A\right)
    \end{align*}
    The naturality of $q_{A,F}$ means that 
    \[
        \begin{tikzcd}[ampersand replacement=\&]
            \mathsf{C}^{\mathrm{op}}\times \left[\mathsf{C}^{\mathrm{op}},\mathsf{Set}\right]\&[-34pt]\&[+62pt]\&[-25pt] \mathsf{Set}\&[-25pt]\&[-25pt] \\ [-15pt] 
            (A_1,F_1)  \arrow[dd, "\left(g{,} \eta\right)"{name=L, left}] 
            \&[-25pt] \& [+10pt] 
            \& [-30pt]\operatorname{Hom}_{\mathsf{Psh}(\mathsf{C})}(\mathrm{Hom}_{\mathsf{C}}(-,A_1),F_1)\arrow[dd, ""{name=R}] \& \ni \& \phi \arrow[dd,mapsto]\\ [-8pt] 
            \&  \phantom{.}\arrow[r, "\operatorname{Hom}_{\mathsf{Psh}(\mathsf{C})}\left(Y_\mathsf{C}(-){,}-\right)", squigarrow]\&\phantom{.}  \&   \\[-8pt] 
            (A_2,F_2)  \& \& \& \operatorname{Hom}_{\mathsf{Psh}(\mathsf{C})}(\mathrm{Hom}_{\mathsf{C}}(-,A_2),F_2)\& \ni \& \eta\circ \phi\circ g_\star
        \end{tikzcd}
    \]
    is a functor isomorphic to the \hyperref[th:evaluation_functor]{evaluation functor}
    \begin{align*}
        \mathrm{ev}:\mathsf{C}^{\mathrm{op}}\times \left[\mathsf{C}^{\mathrm{op}},\mathsf{Set}\right]&\longrightarrow \mathsf{Set}\\
        \left(A,F\right)&\longmapsto F(A)
    \end{align*}
    \textbf{Covariant version}\\
    For any functor $F:\mathsf{C}\to \mathsf{Set}$ and any $A\in \mathrm{Ob}(\mathsf{C})$, there is a natural bijection
    \begin{align*}
        \operatorname{Hom}_{\left[\mathsf{C},\mathsf{Set}\right]}\left(\operatorname{Hom}_{\mathsf{C}}\left(A,-\right), F\right) & \overset{\sim}{\longrightarrow} F(A) \\
        {  \left[ \begin{tikzcd}[ampersand replacement=\&]
            \mathsf{C} \arrow[r, "\operatorname{Hom}_{\mathsf{C}}\left(A{,}-\right)"{name=A, above}, bend left] \arrow[r, "F"'{name=B, below}, bend right] \&[+30pt] \mathsf{Set}
            \arrow[Rightarrow, shorten <=5.5pt, shorten >=5.5pt, from=A.south-|B, to=B, "\phi"]
        \end{tikzcd}\right] } & \longmapsto \phi_A\left(\operatorname{id}_A\right)
    \end{align*}
}
\cor[module_localization_glueing_property_cor]{}{
    Given an $R$-module $M$, the following are equivalent:
    \begin{enumerate}[(i)]
        \item $M$ is zero,
        \item $M_{\mathfrak{p}}$ is zero for all $\mathfrak{p} \in \operatorname{Spec}(R)$,
        \item $M_{\mathfrak{m}}$ is zero for all $\mathfrak{m}\in \mathrm{Max}\left(R\right)$.
    \end{enumerate} 
}

'''

print(process_latex_content(test_input))


filename_list = [
    'set_theory.tex',
    'category_theory.tex',
    'group.tex',
    'topological_group.tex',
    'ring.tex',
    'commutative_ring.tex',
    'module.tex',
    'associative_algebra.tex',
    'field.tex',
    'valuation_theory.tex',
    'number_theory.tex',
]

for input_tex_path in filename_list:
    expand_dfn_macro(input_tex_path)

