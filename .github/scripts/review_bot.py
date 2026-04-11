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
VALID_SCOPES = {"diff", "file"}
COMMAND_RE = re.compile(r"^/review(?:\s+(?P<body>.*))?$", re.DOTALL)
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


def parse_command(comment_body: str) -> tuple[str, list[str]]:
    match = COMMAND_RE.match(comment_body.strip())
    if not match:
        return "diff", []
    tail = (match.group("body") or "").strip()
    if not tail:
        return "diff", []
    try:
        tokens = shlex.split(tail)
    except ValueError as exc:
        fail(f"Unable to parse /review arguments: {exc}")

    scope = "diff"
    paths: list[str] = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token.startswith("--scope="):
            scope = token.split("=", 1)[1]
            i += 1
            continue
        if token == "--scope":
            if i + 1 >= len(tokens):
                fail("Missing value after --scope. Use --scope=diff or --scope=file.")
            scope = tokens[i + 1]
            i += 2
            continue
        paths.append(token)
        i += 1

    if scope not in VALID_SCOPES:
        fail(f"Unsupported scope `{scope}`. Use --scope=diff or --scope=file.")

    return scope, paths


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


def list_repo_files(review_target_dir: Path, path_filters: list[str]) -> list[dict[str, Any]]:
    repo_files: list[dict[str, Any]] = []
    for path in sorted(review_target_dir.rglob("*.lean")):
        if not path.is_file():
            continue
        relative = path.relative_to(review_target_dir).as_posix()
        if path_filters and not any(fnmatch.fnmatch(relative, pattern) for pattern in path_filters):
            continue
        repo_files.append(
            {
                "filename": relative,
                "status": "present",
                "patch": None,
                "changed_lines": [],
                "changed_line_ranges": [],
            }
        )
    return repo_files


def select_file_scope_targets(
    *,
    pr_files: list[dict[str, Any]],
    review_target_dir: Path,
    path_filters: list[str],
) -> list[dict[str, Any]]:
    selected = list_repo_files(review_target_dir, path_filters)
    diff_by_path: dict[str, dict[str, Any]] = {}
    for pr_file in pr_files:
        path = pr_file["filename"]
        if not path.endswith(".lean"):
            continue
        changed_lines = parse_changed_lines(pr_file.get("patch"))
        diff_by_path[path] = {
            "status": pr_file.get("status", "modified"),
            "patch": pr_file.get("patch"),
            "changed_lines": changed_lines,
            "changed_line_ranges": compress_ranges(changed_lines),
        }

    for item in selected:
        overlay = diff_by_path.get(item["filename"])
        if not overlay:
            continue
        item.update(overlay)
    return selected


def toml_string(value: str) -> str:
    return json.dumps(value)


def build_prompt(
    prompt_template: str,
    skill_text: str,
    pr: dict[str, Any],
    selected_files: list[dict[str, Any]],
    review_scope: str,
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
        "review_scope": review_scope,
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

        只针对上面列出的文件做 review。
        如果 `review_scope` 是 `diff`，把注意力集中在 patch 和改动行上。
        如果 `review_scope` 是 `file`，先完整阅读被选中的文件，再决定是否有值得提出的修改。

        GitHub 的 inline suggestion 只能锚定到 PR diff 里的 changed RIGHT-side lines。
        因此，只有当某条建议对应的 `line` / `start_line` 落在该文件
        `changed_line_ranges_on_right_side` 内时，才把它放进 `comments`。
        如果你发现的最佳修改点不在 diff 中，请不要伪造锚点，把它写进 `summary`，并返回空 comments 或只返回其他合法 comments。

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

    review_scope, path_filters = parse_command(comment_body)
    pr_files = github.list_pull_request_files(pull_number)
    if review_scope == "file":
        if not path_filters:
            github.create_issue_comment(
                pull_number,
                "file mode 需要显式指定路径。用法：`/review Ray/Misc/Real.lean --scope=file`。",
            )
            return
        selected_files = select_file_scope_targets(
            pr_files=pr_files,
            review_target_dir=review_target_dir,
            path_filters=path_filters,
        )
    else:
        selected_files = select_files(pr_files, path_filters)

    if not selected_files:
        suffix = ""
        if path_filters:
            suffix = f"（当前过滤条件：`{' '.join(path_filters)}`）"
        if review_scope == "file":
            message = (
                "没有找到匹配的 `.lean` 文件"
                f"{suffix}。可用法：`/review Ray/Foo.lean --scope=file`。"
            )
        else:
            message = (
                "没有找到可 review 的已修改 `.lean` 文件"
                f"{suffix}。可用法：`/review`、`/review Ray/Foo.lean`、`/review Ray/Foo.lean --scope=file`。"
            )
        github.create_issue_comment(
            pull_number,
            message,
        )
        return

    if len(selected_files) > MAX_CHANGED_FILES and not path_filters:
        github.create_issue_comment(
            pull_number,
            "这次 PR 里可 review 的 `.lean` 改动文件太多。"
            " 请用 `/review path/to/File.lean` 或 `/review path/to/File.lean --scope=file` 缩小范围后再触发。",
        )
        return

    prompt_template = (
        bot_repo_root / ".github" / "codex" / "prompts" / "review-file.md"
    ).read_text(encoding="utf-8")
    skill_text = (
        bot_repo_root / ".agents" / "skills" / "pr-inline-review" / "SKILL.md"
    ).read_text(encoding="utf-8")
    prompt = build_prompt(
        prompt_template,
        skill_text,
        pr,
        selected_files,
        review_scope,
        path_filters,
    )

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
            f"Triggered by @{commenter} with `/review` (scope: {review_scope}).\n\n{summary}",
            comments,
        )
        return

    github.create_issue_comment(
        pull_number,
        f"@{commenter} review 完成（scope: {review_scope}），但这次没有生成可直接应用的 inline suggestion。\n\n{summary}",
    )


if __name__ == "__main__":
    main()
