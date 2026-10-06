from __future__ import annotations
from typing import Any

from clarify.env import ClarificationEnvironment, TooManyQuestionException
from clarify.baselines.base import ClarificationAlgorithmBase
from clarify.runtime import _validate_and_parse_evalplus_result


class QuickStartClarification(ClarificationAlgorithmBase):
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