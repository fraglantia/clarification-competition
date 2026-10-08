# SPDX-FileCopyrightText: 2026 Steve Gustaman <stevegustaman@softsec.kaist.ac.kr>
#
# SPDX-License-Identifier: MIT

"""Prototype 2 algorithm name.

Fill in here later with a description of the algorithm.

Team: SoftSec
Team Members: Member 1, Member 2, ...
Main Contact: main.contact@example.com
"""

from __future__ import annotations

from typing import Any

from clarify.baselines.base import ClarificationAlgorithmBase
from clarify.env import ClarificationEnvironment, TooManyQuestionException
from clarify.runtime import _validate_and_parse_evalplus_result


class SoftSecPrototypeClarifier(ClarificationAlgorithmBase):
    def run(self, env: ClarificationEnvironment, problem: dict[str, Any]) -> str:
        messages = [{"role": "user", "content": problem["prompt"]}]

        response = env.llm(messages)

        messages += [{"role": "assistant", "content": response}]

        while True:
            try:
                return _validate_and_parse_evalplus_result(response)
            except ValueError:
                # The response might not contain an answer, assume a question is raised.
                try:
                    answer = env.ask_human(response)
                    messages += [{"role": "user", "content": answer}]
                    response = env.llm(messages)
                    messages += [{"role": "assistant", "content": response}]
                except TooManyQuestionException:
                    return response
