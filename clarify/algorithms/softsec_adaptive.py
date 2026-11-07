# SPDX-FileCopyrightText: 2026 Steve Gustaman <stevegustaman@softsec.kaist.ac.kr>
#
# SPDX-License-Identifier: MIT

"""SoftSecAdaptive: restate the draft, ask what must change, revise until confirmed.

Draft code under the most conventional reading of the task, restate in plain words what the draft
does (never the code), and ask the user what must change in that understanding. Every reply is kept
as a requirement: the code is revised against all replies so far and the updated restatement is shown
again, until the user confirms, a reply changes nothing, or max_questions is reached.

If the first replies to the broad question are mostly vague (a Beta estimate of the share of concrete
replies, kept as three integers shared across worker processes), later tasks ask a focused question
for one fact at a time. Nothing about any task's content is kept across tasks.

Pipeline per task: draft (plan, then code) -> restate -> ask -> read the reply (one-word label) ->
revise against all replies -> repeat -> finalize (definitions only, `from __future__ import
annotations`, lower-case alias of the entry point, and a call wrapper that runs the direct call first
and only retries with adjusted arguments if it raises).

Team: SoftSec
Team Members: Steve Gustaman (KAIST), Jungwoo Lee (KAIST), Jinheon Lee (KAIST), Dongwoo Kim (KAIST)
Main Contact: Steve Gustaman, stevegustaman@softsec.kaist.ac.kr
"""

from __future__ import annotations

import ast
import hashlib
import json
import multiprocessing
import os
import re
import tempfile
import threading
from math import comb
from typing import Any

try:
    import fcntl
except ImportError:  # not available on Windows: the count then stays per process
    fcntl = None

from clarify.baselines import ClarificationAlgorithmBase
from clarify.env import ClarificationEnvironment, LimitsExceededException, TooManyQuestionException
from clarify.runtime import _validate_and_parse_evalplus_result

SOLVE_PROMPT = """
Implement `{entry_point}` in Python for the task below.

Rules:
- Define functions only. No `input()`, no printing, no `if __name__ == "__main__":` block,
  no example usage.
- The function must be named exactly `{entry_point}`.
- Use the most conventional reading of the task. The task text may have been altered: one
  sentence may contradict the rest, an example may show a wrong output, or names may be
  generic. Infer the original task: follow what the function name, the type hints, domain
  conventions and the rest of the text agree on, and treat the single conflicting sentence
  or example as the error.
{feedback}
Task:
{prompt}

Before the code, write a short plan: the exact call signature and argument order the tests
most likely use, the input types, the exact return type and format (container, literal
strings or values), the core rule, and how edge cases behave. Write the plan as plain text
with no code blocks. Then give the code in a single ```python ... ``` block.
""".strip()

RESTATE_PROMPT = """
Describe exactly what this Python implementation of `{entry_point}` does, so that someone who
cannot see the code could predict its output for any input. Use at most 8 short numbered
statements in plain words, without code and without variable names. Include the argument order
and type of each argument, the exact return type and format (container, separators, literal
strings or values), every condition, boundary, constant, ordering or direction it uses, and what
happens on edge cases. State only what the code does, even where it looks wrong.

```python
{code}
```

Reply with the numbered list only.
""".strip()

RESTATE_QUESTION = """Here is how I understand the task:
{spec}
Is this what you need? If not, what is the one thing I must change about how I understand it?"""

RESTATE_ASK = (
    "Is this what you need? If not, what is the one thing I must change about how I understand it?"
)

NEXT_RESTATE_QUESTION = """Here is how I understand the task now:
{spec}
Is this what you need now? If not, what is the one thing I must still change about how I understand it?"""

NEXT_RESTATE_ASK = "Is this what you need now? If not, what is the one thing I must still change about how I understand it?"

# Appended to every question: ask for the exact correction, and only for what the requirements state.
ASK_LINES = (
    "If something must change, say exactly what it must be instead (the correct value, rule or format); "
    "do not just name the part that is wrong or ask me to clarify. Only point out something your requirements "
    "actually state. If nothing you know of is wrong, just say yes."
)

# Added to broad questions: when several points are wrong, ask for the one with the widest effect first.
PRIORITY_LINE = "If several things must change, name the one that affects the most inputs."


PROPOSAL_PROMPT = """Describe exactly what this Python implementation of `{entry_point}` does, so that someone who
cannot see the code could predict its output for any input. Use at most 8 short statements in plain words,
without code and without variable names, in this order: first the core rule (what the result is computed
from and how), then the exact return type and format (container, separators, literal strings or values),
then the arguments (their order and type), then every remaining condition, boundary, constant, ordering or
direction it uses, and what happens on edge cases. State only what the code does, even where it looks wrong.

```python
{code}
```

Reply with the statements only, one per line."""

FIRST_QUESTION = "I propose to solve the task like this: {proposal}\n{tail}"

NEXT_QUESTION = "Here is my updated proposal: {proposal}\n{tail}"

QUESTION_TAIL = (
    "Before I implement it: reading my proposal from the start, what is the first point that your requirements "
    "settle differently? Tell me only what your requirements say for that one point (one fact: a value, rule or "
    "format), not code or test cases. Write names and values as plain words, not as code."
)

# Reads the user's reply: does it only confirm (or give nothing to act on)? Answered with one word.
CONFIRMATION_PROMPT = """
We showed a user, who knows the real requirements of a coding task, our current solution and asked:
"{ask}"
The user replied:
"{answer}"

Is this reply only a confirmation or a non-answer?
- Answer YES if the reply says that our solution already matches or is correct, or that nothing
  differs or nothing needs to change (it may also restate what the solution already does), or if it
  declines to answer, asks a question back, or gives no usable information. Examples: "Yes, that is
  what I need." / "Your proposal is aligned; there is no point that differs." / "I can't say."
- Answer NO if the reply states any requirement, value, format, rule, argument, name or other fact, or
  points at something to get right, even briefly. Examples: "The second argument is a list." /
  "Repeated words are left unchanged." / "Be careful with how ties are ordered."
- A reply that names a part of the solution that still differs or needs care, even without saying
  how (for example "The remaining difference is in the output format."), is NO.

Reply with exactly one word: YES or NO.
""".strip()

# Reads the first reply to a broad question for the running count. Answered with one word.
ANSWER_STYLE_PROMPT = """
We described our solution of a coding task to a user, who knows the real requirements, and asked:
"{ask}"
The user replied:
"{answer}"

Classify the reply with exactly one word:
- CONFIRM if it says our description is right or that nothing needs to change (for example "Yes." or "That matches").
- FACT if it states exactly what must be different: a concrete value, output format, rule, name, argument or
  behaviour for a specific case, precise enough to implement without guessing (for example "Return the string
  'No solution' when there is none" or "Use the function name sort_even").
- HINT if it says something differs or matters, or names the area, without stating exactly what it must be (for
  example "One key behavior around mismatched lengths differs" or "Mostly yes, but one assumption does not hold"),
  or if it declines or asks to ask separately.
""".strip()

# How the revision block refers to the question, per presentation.
ASKED_BROAD = "what must change"
ASKED_FOCUSED = "what their requirements settle differently"

# Revision prompt: every reply so far is a standing requirement; the coder checks each against the current code.
REVISE_ALL_BLOCK = """
Current implementation:
```python
{code}
```
You showed the user, who knows the real requirements, a plain-language description of your solution and asked
{asked}. The user's replies so far, oldest first:
{replies}
Your latest question was:
"{question}"

Each reply is a requirement. A reply overrides the task text: where a task sentence or example contradicts a
reply, follow the reply and treat that task sentence or example as the altered part. Every reply stays in force,
not only the latest one: if the current implementation no longer satisfies an earlier reply, fix that too.
Change nothing that no reply asks to change. The function must keep the name `{entry_point}`. If a reply says
the function must have another name, keep `{entry_point}` and add that name as an alias after it
(`other_name = {entry_point}`); a remark about the name changes nothing else. If the current implementation
already satisfies every reply, return it unchanged apart from such an alias.
"""
REVISE_PLAN = (
    "Before the code, write a short plan as plain text with no code blocks: go through the user's replies one\n"
    "by one and say whether the current implementation satisfies each one exactly, and if not, what must change.\n"
    "Then give the complete code in a single ```python ... ``` block."
)
REVISE_PROMPT = (
    SOLVE_PROMPT[: SOLVE_PROMPT.index("Before the code, write a short plan")] + REVISE_PLAN
)

EMPTY = "def {entry_point}(*args, **kwargs):\n    raise NotImplementedError\n"

FUTURE_IMPORT = "from __future__ import annotations\n"

HEDGE_TEMPLATE = '''

import copy as hedge_copy_
import inspect as hedge_inspect_

hedge_impl_ = ENTRY_POINT
hedge_depth_ = [0]


def hedge_candidates_(args):
    """Alternative argument tuples to try when the direct call raises."""
    out = []
    try:
        sig = hedge_inspect_.signature(hedge_impl_)
    except (TypeError, ValueError):
        sig = None
    if sig is not None:
        kinds = [p.kind for p in sig.parameters.values()]
        positional = [p for p in sig.parameters.values() if p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD)]
        required = [p for p in positional if p.default is p.empty]
        has_var = hedge_inspect_.Parameter.VAR_POSITIONAL in kinds
        if len(args) < len(required):
            out.append(tuple(args) + (None,) * (len(required) - len(args)))
        if not has_var and len(args) > len(positional):
            if len(positional) == 1:
                out.append((tuple(args),))
            out.append(tuple(args[: len(positional)]))
        if len(args) == 1 and isinstance(args[0], (list, tuple)) and len(args[0]) == len(required) > 1:
            out.append(tuple(args[0]))
    if len(args) == 2:
        out.append((args[1], args[0]))
    return out


def ENTRY_POINT(*args, **kwargs):
    if hedge_depth_[0] > 0:
        return hedge_impl_(*args, **kwargs)
    try:
        snapshot = hedge_copy_.deepcopy(args)
    except Exception:
        snapshot = None
    hedge_depth_[0] += 1
    try:
        try:
            return hedge_impl_(*args, **kwargs)
        except Exception as first_error:
            if snapshot is None:
                raise
            for candidate in hedge_candidates_(snapshot):
                try:
                    return hedge_impl_(*hedge_copy_.deepcopy(candidate), **kwargs)
                except Exception:
                    continue
            raise first_error
    finally:
        hedge_depth_[0] -= 1
'''

CODE_STARTS = ("def ", "async def ", "class ", "import ", "from ", "@")


PYTHON_FENCE = re.compile(r"```python[ \t]*\r?\n(.*?)```", re.DOTALL)


def defined_functions(code: str) -> set[str] | None:
    """Names of the top-level functions in code, or None when it does not parse."""
    try:
        tree = ast.parse(code)
    except (SyntaxError, RecursionError, ValueError):
        return None
    return {n.name for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}


def extract_code(response: str, entry_point: str | None = None) -> str | None:
    """The solution's fenced python block from an LLM reply, or None.

    A reply sometimes holds more than one block (a snippet in the plan, then the solution), so the
    last block that defines the entry point is taken, else the last block that defines any
    function, else the first block. A reply without a fence is accepted when, from its first line
    that starts a definition or import, the rest is valid Python that defines a function (some
    models answer with bare code instead of a fenced block)."""
    blocks = PYTHON_FENCE.findall(response or "")
    defining = [(b, defined_functions(b)) for b in blocks]
    for wanted in (entry_point, None):
        for block, names in reversed(defining):
            if names and (wanted is None or wanted in names):
                return block
    try:
        return _validate_and_parse_evalplus_result(response)
    except ValueError:
        pass
    lines = (response or "").splitlines()
    for i, line in enumerate(lines):
        if line.startswith(CODE_STARTS):
            code = "\n".join(lines[i:]).strip()
            try:
                tree = ast.parse(code)
            except (SyntaxError, RecursionError):
                return None
            if any(isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) for node in tree.body):
                return code + "\n"
            return None
    return None


def only_confirms(env: ClarificationEnvironment, ask: str, answer: str) -> bool:
    """True when the reply only confirms our solution or gives nothing to act on. One env.llm
    call reads the reply; only its one-word verdict is checked here."""
    if not (answer or "").strip():
        return True
    verdict = env.llm(CONFIRMATION_PROMPT.format(ask=ask, answer=answer.strip()))
    return "YES" in verdict.strip().upper()


def finalize(code: str, entry_point: str) -> str:
    """finalize_tree, with code too deeply nested for the parser or unparser counted as no code."""
    try:
        return finalize_tree(code, entry_point)
    except RecursionError:
        return EMPTY.format(entry_point=entry_point)


def finalize_tree(code: str, entry_point: str) -> str:
    """Keep only definitions, imports and assignments, and make sure the entry point exists
    (aliasing a renamed function if needed)."""
    try:
        tree = ast.parse(code)
    except (SyntaxError, RecursionError):
        return EMPTY.format(entry_point=entry_point)

    keep: list[ast.stmt] = []
    for node in tree.body:
        if isinstance(
            node,
            (
                ast.FunctionDef,
                ast.AsyncFunctionDef,
                ast.ClassDef,
                ast.Import,
                ast.ImportFrom,
                ast.Assign,
                ast.AnnAssign,
            ),
        ):
            src = ast.get_source_segment(code, node) or ""
            if isinstance(node, (ast.Assign, ast.AnnAssign)) and re.search(
                r"\binput\s*\(|\bprint\s*\(", src
            ):
                continue
            keep.append(node)

    funcs = [n.name for n in keep if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    tree.body = keep
    if entry_point in funcs:
        return ast.unparse(tree) + "\n"
    if not funcs:
        return EMPTY.format(entry_point=entry_point)

    def norm(name: str) -> str:
        return re.sub(r"[^a-z0-9]", "", name.lower())

    alias = (
        funcs[0]
        if len(funcs) == 1
        else next((f for f in funcs if norm(f) == norm(entry_point)), funcs[-1])
    )
    return ast.unparse(tree) + f"\n\n{entry_point} = {alias}\n"


def hedge(code: str, entry_point: str) -> str:
    """Wrap the entry point so a call-shape mismatch is retried with alternative arguments."""
    return code.rstrip() + "\n" + HEDGE_TEMPLATE.replace("ENTRY_POINT", entry_point)


def wrap(code: str) -> str:
    return f"```python\n{code}\n```"


def as_prose(statements: str) -> str:
    """Join the one-statement-per-line description into one paragraph."""
    items = [line.strip() for line in statements.strip().splitlines()]
    return " ".join(s if s.endswith((".", "!", "?")) else s + "." for s in items if s)


def same_code(a: str, b: str) -> bool:
    """True when two versions differ only in layout or comments: their syntax trees are equal."""
    try:
        return ast.dump(ast.parse(a)) == ast.dump(ast.parse(b))
    except (SyntaxError, RecursionError):
        return a.strip() == b.strip()


def p_share_below(concrete: int, vague: int, threshold: float) -> float:
    """P(p < threshold) for p ~ Beta(concrete + 1, vague + 1), via the Binomial identity."""
    n = concrete + vague + 1
    return sum(
        comb(n, k) * threshold**k * (1 - threshold) ** (n - k) for k in range(concrete + 1, n + 1)
    )


class RunningCount:
    """The count of how the user answers broad questions: concrete and vague first replies, and focused tasks so far.

    Kept in memory with shared=False. With shared=True and when running in a worker process of a multiprocessing pool, it is
    kept in one small file in the system temp directory instead, named after the run's main process (a hash of its
    random multiprocessing key, which every worker of the run inherits), so all workers of one run share it and a new
    run starts from zero. The file holds only the three numbers. The shared file is best effort: if no temp directory
    is usable, or the file cannot be opened, locked, read, parsed or written, this worker keeps counting in memory for
    the rest of its life, as with shared=False. No error from the file ever reaches the algorithm."""

    KEYS = ("concrete", "vague", "focused_tasks")

    def __init__(self, shared: bool):
        self.lock = threading.Lock()
        self.memory = dict.fromkeys(self.KEYS, 0)
        self.path = None
        if not shared or fcntl is None:
            return
        try:
            if multiprocessing.parent_process() is None:
                return  # not a pool worker: nothing to share with
            run = hashlib.sha256(bytes(multiprocessing.current_process().authkey)).hexdigest()[:16]
            self.path = os.path.join(tempfile.gettempdir(), f"softsec_adaptive_{run}.json")
        except Exception:  # e.g. no usable temp directory: count in memory
            self.path = None

    def update(self, change):
        """Apply change(counts) atomically and return its result."""
        with self.lock:
            if self.path is not None:
                try:
                    return self.update_file(change)
                except Exception:  # any file problem: count in memory from now on
                    self.path = None
            return change(self.memory)

    def update_file(self, change):
        fd = os.open(self.path, os.O_RDWR | os.O_CREAT, 0o600)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX)  # released when the file is closed
            raw = os.read(fd, 1024)
            counts = json.loads(raw) if raw else dict.fromkeys(self.KEYS, 0)
            if not (
                isinstance(counts, dict) and all(type(counts.get(k)) is int for k in self.KEYS)
            ):
                raise ValueError("unexpected count file content")
            result = change(counts)
            os.lseek(fd, 0, os.SEEK_SET)
            os.ftruncate(fd, 0)
            os.write(fd, json.dumps(counts).encode())
            return result
        finally:
            os.close(fd)


COUNT_SETUP_LOCK = threading.Lock()  # guards creating an algorithm object's running count


class SoftSecAdaptive(ClarificationAlgorithmBase):
    DEFAULT_CONFIG = {
        # most questions per task, in both presentations; the environment's max_clarification_turns also caps it
        "max_questions": 10,
        "focused_questions": "auto",  # "auto" (learned from the replies), True (always focused) or False (always broad)
        "fact_share": 0.6,  # switch to focused questions once the share of concrete first replies is likely below this
        "confidence": 0.99,  # how likely it must be
        "explore_every": 20,  # while focused, every n-th task still asks broadly so the count stays current
        # keep the running count in one small file per run, so worker processes of the same run share it
        "shared_count": True,
        # add PRIORITY_LINE to broad questions (more first replies state a concrete fact)
        "priority_line": True,
    }

    def running_count(self) -> RunningCount:
        """The running count, created on first use (one per algorithm object)."""
        with COUNT_SETUP_LOCK:
            if getattr(self, "answer_count", None) is None:
                self.answer_count = RunningCount(shared=self.config["shared_count"])
            return self.answer_count

    def choose_focused(self) -> bool:
        setting = self.config["focused_questions"]
        if setting != "auto":
            return bool(setting)

        def decide(c: dict[str, int]) -> bool:
            if (
                p_share_below(c["concrete"], c["vague"], self.config["fact_share"])
                <= self.config["confidence"]
            ):
                return False
            c["focused_tasks"] += 1
            return c["focused_tasks"] % self.config["explore_every"] != 0

        return self.running_count().update(decide)

    def record_first_reply(self, env: ClarificationEnvironment, ask: str, answer: str) -> None:
        verdict = (
            env.llm(ANSWER_STYLE_PROMPT.format(ask=ask, answer=answer.strip())).strip().upper()
        )
        label = next((t for t in ("CONFIRM", "FACT", "HINT") if t in verdict), "HINT")

        def add(c: dict[str, int]) -> None:
            c["concrete"] += label == "FACT"
            c["vague"] += label == "HINT"

        self.running_count().update(add)

    def draft(self, env: ClarificationEnvironment, entry_point: str, prompt: str) -> str:
        resp = env.llm(SOLVE_PROMPT.format(entry_point=entry_point, prompt=prompt, feedback=""))
        return extract_code(resp, entry_point) or EMPTY.format(entry_point=entry_point)

    def describe(
        self, env: ClarificationEnvironment, entry_point: str, code: str, focused: bool
    ) -> str:
        if focused:
            return as_prose(env.llm(PROPOSAL_PROMPT.format(entry_point=entry_point, code=code)))
        return env.llm(RESTATE_PROMPT.format(entry_point=entry_point, code=code)).strip()

    def question(self, description: str, focused: bool, first: bool) -> tuple[str, str]:
        """The question to send and the part of it the reply answers."""
        if focused:
            template = FIRST_QUESTION if first else NEXT_QUESTION
            return template.format(proposal=description, tail=QUESTION_TAIL), QUESTION_TAIL
        template, ask = (
            (RESTATE_QUESTION, RESTATE_ASK) if first else (NEXT_RESTATE_QUESTION, NEXT_RESTATE_ASK)
        )
        lines = ASK_LINES + (" " + PRIORITY_LINE if self.config["priority_line"] else "")
        return template.format(spec=description) + " " + lines, ask + " " + lines

    def ask(self, env: ClarificationEnvironment, question: str) -> str | None:
        if not env.can_ask():
            return None
        try:
            return env.ask_human(question)
        except TooManyQuestionException:
            return None

    def revise(self, env, entry_point, prompt, code, question, replies, focused):
        numbered = "\n".join(f'{i}. "{r}"' for i, r in enumerate(replies, 1))
        block = REVISE_ALL_BLOCK.format(
            code=code,
            replies=numbered,
            question=question,
            entry_point=entry_point,
            asked=ASKED_FOCUSED if focused else ASKED_BROAD,
        )
        for _ in range(2):
            new = extract_code(
                env.llm(
                    REVISE_PROMPT.format(entry_point=entry_point, prompt=prompt, feedback=block)
                ),
                entry_point,
            )
            if (
                new
                and "NotImplementedError" not in code
                and "NotImplementedError" in finalize(new, entry_point)
            ):
                continue  # unparsable, function-less or stub code would replace working code with a stub
            if new:
                return new
        return code

    def run(self, env: ClarificationEnvironment, problem: dict[str, Any]) -> str:
        entry_point, prompt = problem["entry_point"], problem["prompt"]
        code = EMPTY.format(entry_point=entry_point)
        replies: list[str] = []
        try:
            focused = self.choose_focused()
            code = finalize(self.draft(env, entry_point, prompt), entry_point)
            while len(replies) < self.config["max_questions"] and env.can_ask():
                description = self.describe(env, entry_point, code, focused)
                question, ask = self.question(description, focused, not replies)
                answer = self.ask(env, question)
                if answer is None:
                    break
                if (
                    not replies
                    and not focused
                    and self.config["focused_questions"] == "auto"
                    and answer.strip()
                ):
                    self.record_first_reply(env, ask, answer)
                if only_confirms(env, ask, answer):
                    break  # confirmed or declined: revising would only risk breaking the code
                replies.append(answer)
                revised = finalize(
                    self.revise(env, entry_point, prompt, code, question, replies, focused),
                    entry_point,
                )
                if same_code(revised, code):
                    break  # nothing changed: asking again would show the same description
                code = revised
        except LimitsExceededException:
            pass
        final = FUTURE_IMPORT + hedge(code, entry_point)
        if entry_point.lower() != entry_point:
            # tests sometimes call the all-lowercase spelling of a name that has capitals
            final += f"\n{entry_point.lower()} = {entry_point}\n"
        return wrap(final)
