#!/usr/bin/env python3
from __future__ import annotations

import fnmatch
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import textwrap
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


API_VERSION = "2022-11-28"
MAX_CHANGED_FILES = 8
MAX_COMMENTS = 6
COMMAND_RE = re.compile(r"^/review(?:\s+file)?(?:\s+(?P<paths>.*))?$", re.DOTALL)
HUNK_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(?P<start>\d+)(?:,(?P<count>\d+))? @@")


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(1)


class GitHubClient:
    def __init__(self, token: str, repository: str) -> None:
        self.token = token
        self.owner, self.repo = repository.split("/", 1)

    def request(
        self,
        method: str,
        path_or_url: str,
        payload: dict[str, Any] | None = None,
    ) -> Any:
        url = path_or_url
        if not path_or_url.startswith("https://"):
            url = f"https://api.github.com{path_or_url}"

        body = None
        if payload is not None:
            body = json.dumps(payload).encode("utf-8")

        request = urllib.request.Request(
            url,
            data=body,
            method=method,
            headers={
                "Accept": "application/vnd.github+json",
                "Authorization": f"Bearer {self.token}",
                "User-Agent": "codex-pr-inline-review-bot",
                "X-GitHub-Api-Version": API_VERSION,
            },
        )

        try:
            with urllib.request.urlopen(request) as response:
                raw = response.read().decode("utf-8")
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            fail(f"GitHub API {exc.code} for {url}: {detail}")

        if not raw:
            return None
        return json.loads(raw)

    def get_pull_request(self, number: int) -> dict[str, Any]:
        return self.request("GET", f"/repos/{self.owner}/{self.repo}/pulls/{number}")

    def list_pull_request_files(self, number: int) -> list[dict[str, Any]]:
        files: list[dict[str, Any]] = []
        page = 1
        while True:
            response = self.request(
                "GET",
                f"/repos/{self.owner}/{self.repo}/pulls/{number}/files"
                f"?per_page=100&page={page}",
            )
            if not response:
                break
            files.extend(response)
            if len(response) < 100:
                break
            page += 1
        return files

    def create_issue_comment(self, number: int, body: str) -> None:
        self.request(
            "POST",
            f"/repos/{self.owner}/{self.repo}/issues/{number}/comments",
            {"body": body},
        )

    def create_review(
        self,
        number: int,
        commit_id: str,
        body: str,
        comments: list[dict[str, Any]],
    ) -> None:
        payload: dict[str, Any] = {
            "commit_id": commit_id,
            "body": body,
            "event": "COMMENT",
        }
        if comments:
            payload["comments"] = comments
        self.request(
            "POST",
            f"/repos/{self.owner}/{self.repo}/pulls/{number}/reviews",
            payload,
        )


def parse_command(comment_body: str) -> list[str]:
    match = COMMAND_RE.match(comment_body.strip())
    if not match:
        return []
    tail = (match.group("paths") or "").strip()
    if not tail:
        return []
    try:
        return shlex.split(tail)
    except ValueError as exc:
        fail(f"Unable to parse /review file arguments: {exc}")


def parse_changed_lines(patch: str | None) -> list[int]:
    if not patch:
        return []

    changed_lines: list[int] = []
    new_line = 0

    for raw_line in patch.splitlines():
        if raw_line.startswith("@@"):
            match = HUNK_RE.match(raw_line)
            if not match:
                continue
            new_line = int(match.group("start"))
            continue

        if raw_line.startswith("+++ ") or raw_line.startswith("--- "):
            continue
        if raw_line.startswith("\\"):
            continue
        if raw_line.startswith("+"):
            changed_lines.append(new_line)
            new_line += 1
            continue
        if raw_line.startswith("-"):
            continue
        new_line += 1

    return changed_lines


def compress_ranges(lines: list[int]) -> list[list[int]]:
    if not lines:
        return []

    result: list[list[int]] = []
    start = lines[0]
    end = lines[0]

    for line in lines[1:]:
        if line == end + 1:
            end = line
            continue
        result.append([start, end])
        start = line
        end = line

    result.append([start, end])
    return result


def select_files(
    pr_files: list[dict[str, Any]],
    path_filters: list[str],
) -> list[dict[str, Any]]:
    eligible: list[dict[str, Any]] = []
    for pr_file in pr_files:
        path = pr_file["filename"]
        if pr_file.get("status") == "removed":
            continue
        if not path.endswith(".lean"):
            continue
        if not pr_file.get("patch"):
            continue
        if path_filters and not any(fnmatch.fnmatch(path, pattern) for pattern in path_filters):
            continue
        changed_lines = parse_changed_lines(pr_file.get("patch"))
        if not changed_lines:
            continue
        pr_file = dict(pr_file)
        pr_file["changed_lines"] = changed_lines
        pr_file["changed_line_ranges"] = compress_ranges(changed_lines)
        eligible.append(pr_file)
    return eligible


def toml_string(value: str) -> str:
    return json.dumps(value)


def build_prompt(
    prompt_template: str,
    skill_text: str,
    pr: dict[str, Any],
    selected_files: list[dict[str, Any]],
    path_filters: list[str],
) -> str:
    context = {
        "pull_request": {
            "number": pr["number"],
            "title": pr["title"],
            "base_ref": pr["base"]["ref"],
            "head_ref": pr["head"]["ref"],
            "base_sha": pr["base"]["sha"],
            "head_sha": pr["head"]["sha"],
        },
        "requested_path_filters": path_filters,
        "files": [
            {
                "path": file["filename"],
                "status": file["status"],
                "changed_line_ranges_on_right_side": file["changed_line_ranges"],
                "patch": file["patch"],
            }
            for file in selected_files
        ],
    }

    return textwrap.dedent(
        f"""
        {prompt_template.strip()}

        以下是必须遵守的 skill 指令内容，来源于 `.agents/skills/pr-inline-review/SKILL.md`：

        <skill>
        {skill_text.strip()}
        </skill>

        当前 PR 上下文如下。你可以在当前工作区读取文件，并可调用 `lean_lsp` MCP。

        <context_json>
        {json.dumps(context, ensure_ascii=False, indent=2)}
        </context_json>

        只针对上面列出的文件做 review。评论必须锚定到对应文件 `changed_line_ranges_on_right_side`
        内的行号，`line` 与 `start_line` 都必须落在这些范围内。不要输出范围外的评论。

        如果没有合适的 inline suggestion，返回空 comments，并在 `summary` 里简短说明原因。
        """
    ).strip()


def run_codex(
    *,
    bot_repo_root: Path,
    review_target_dir: Path,
    prompt: str,
    model: str | None,
) -> dict[str, Any]:
    schema_path = bot_repo_root / ".github" / "codex" / "schema" / "review-file-output.schema.json"
    with tempfile.TemporaryDirectory(prefix="codex-review-") as tmp_dir_name:
        output_path = Path(tmp_dir_name) / "output.json"
        command = [
            "codex",
            "exec",
            "-C",
            str(review_target_dir),
            "-s",
            "workspace-write",
            "--output-schema",
            str(schema_path),
            "-o",
            str(output_path),
            "-c",
            f"mcp_servers.lean_lsp.cwd={toml_string(str(review_target_dir))}",
            "-c",
            "mcp_servers.lean_lsp.args=[\"lean-lsp-mcp\"]",
            "-c",
            f"mcp_servers.lean_lsp.env.LEAN_PROJECT_PATH={toml_string(str(review_target_dir))}",
            "-",
        ]
        if model:
            command[4:4] = ["-m", model]

        completed = subprocess.run(
            command,
            input=prompt,
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode != 0:
            fail(
                "Codex exec failed.\n"
                f"stdout:\n{completed.stdout}\n"
                f"stderr:\n{completed.stderr}"
            )

        if not output_path.exists():
            fail("Codex did not produce an output file.")

        return json.loads(output_path.read_text(encoding="utf-8"))


def sanitize_comment_body(body: str, suggestion: str) -> str:
    clean_body = body.strip()
    clean_suggestion = suggestion.strip("\n")
    return f"{clean_body}\n\n```suggestion\n{clean_suggestion}\n```"


def validate_and_format_comments(
    raw_comments: list[dict[str, Any]],
    valid_lines_by_path: dict[str, set[int]],
) -> list[dict[str, Any]]:
    formatted: list[dict[str, Any]] = []
    seen: set[tuple[str, int | None, int]] = set()

    for raw in raw_comments[:MAX_COMMENTS]:
        path = raw["path"]
        line = int(raw["line"])
        start_line = raw["start_line"]
        if start_line is not None:
            start_line = int(start_line)

        valid_lines = valid_lines_by_path.get(path)
        if not valid_lines or line not in valid_lines:
            continue
        if start_line is not None:
            if start_line > line or start_line not in valid_lines:
                continue

        key = (path, start_line, line)
        if key in seen:
            continue
        seen.add(key)

        body = sanitize_comment_body(raw["body"], raw["suggestion"])
        comment: dict[str, Any] = {
            "path": path,
            "line": line,
            "side": "RIGHT",
            "body": body,
        }
        if start_line is not None and start_line != line:
            comment["start_line"] = start_line
            comment["start_side"] = "RIGHT"
        formatted.append(comment)

    return formatted


def main() -> None:
    repository = os.environ["GITHUB_REPOSITORY"]
    github_token = os.environ["GITHUB_TOKEN"]
    bot_repo_root = Path(os.environ["BOT_REPO_ROOT"]).resolve()
    review_target_dir = Path(os.environ["REVIEW_TARGET_DIR"]).resolve()
    review_model = os.environ.get("REVIEW_MODEL")
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))

    pull_number = int(event["issue"]["number"])
    comment_body = event["comment"]["body"]
    commenter = event["comment"]["user"]["login"]

    github = GitHubClient(github_token, repository)
    pr = github.get_pull_request(pull_number)

    if pr["head"]["repo"]["full_name"] != repository:
        github.create_issue_comment(
            pull_number,
            "出于安全原因，这个 review bot 目前只对同仓库分支的 PR 运行。"
            " 外部 fork 的 PR 不会启动 `lean_lsp` / Codex review。",
        )
        return

    path_filters = parse_command(comment_body)
    pr_files = github.list_pull_request_files(pull_number)
    selected_files = select_files(pr_files, path_filters)

    if not selected_files:
        suffix = ""
        if path_filters:
            suffix = f"（当前过滤条件：`{' '.join(path_filters)}`）"
        github.create_issue_comment(
            pull_number,
            "没有找到可 review 的已修改 `.lean` 文件"
            f"{suffix}。可用法：`/review`、`/review file`、`/review Ray/Foo.lean`。",
        )
        return

    if len(selected_files) > MAX_CHANGED_FILES and not path_filters:
        github.create_issue_comment(
            pull_number,
            "这次 PR 里可 review 的 `.lean` 改动文件太多。"
            " 请用 `/review path/to/File.lean` 或 `/review file path/to/File.lean` 缩小范围后再触发。",
        )
        return

    prompt_template = (
        bot_repo_root / ".github" / "codex" / "prompts" / "review-file.md"
    ).read_text(encoding="utf-8")
    skill_text = (
        bot_repo_root / ".agents" / "skills" / "pr-inline-review" / "SKILL.md"
    ).read_text(encoding="utf-8")
    prompt = build_prompt(prompt_template, skill_text, pr, selected_files, path_filters)

    response = run_codex(
        bot_repo_root=bot_repo_root,
        review_target_dir=review_target_dir,
        prompt=prompt,
        model=review_model,
    )

    summary = str(response.get("summary", "")).strip() or "Inline review completed."
    valid_lines_by_path = {
        file["filename"]: set(file["changed_lines"])
        for file in selected_files
    }
    comments = validate_and_format_comments(
        list(response.get("comments", [])),
        valid_lines_by_path,
    )

    if comments:
        github.create_review(
            pull_number,
            pr["head"]["sha"],
            f"Triggered by @{commenter} with `/review`.\n\n{summary}",
            comments,
        )
        return

    github.create_issue_comment(
        pull_number,
        f"@{commenter} review 完成，但这次没有生成可直接应用的 inline suggestion。\n\n{summary}",
    )


if __name__ == "__main__":
    main()
