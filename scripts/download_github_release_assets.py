#!/usr/bin/env python3
"""Download the exact public Comparator asset triplet from a GitHub release."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
import urllib.error
import urllib.parse
import urllib.request


RELEASE = "v0.48.1"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
MAX_ASSET_BYTES = 2 << 30


class DownloadError(RuntimeError):
    pass


def new_regular_output(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() or path.is_symlink():
        raise DownloadError(f"download target must be new: {path}")
    return path.open("xb")


def request(url: str, token: str, accept: str):
    parsed = urllib.parse.urlparse(url)
    if parsed.scheme != "https" or parsed.hostname != "api.github.com":
        raise DownloadError(f"refusing non-GitHub API URL: {url}")
    return urllib.request.Request(
        url,
        headers={
            "Accept": accept,
            "Authorization": f"Bearer {token}",
            "User-Agent": "paper-c-post-publication-verifier/1",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )


def load_json(url: str, token: str) -> dict:
    with urllib.request.urlopen(request(url, token, "application/vnd.github+json")) as response:
        if response.geturl() != url:
            raise DownloadError("release metadata request unexpectedly redirected")
        payload = response.read(4 << 20)
        if response.read(1):
            raise DownloadError("release metadata exceeds size limit")
    value = json.loads(payload)
    if not isinstance(value, dict):
        raise DownloadError("release metadata is not an object")
    return value


def download(url: str, token: str, destination: Path) -> tuple[int, str]:
    digest = hashlib.sha256()
    observed = 0
    with urllib.request.urlopen(request(url, token, "application/octet-stream")) as response:
        final = urllib.parse.urlparse(response.geturl())
        if final.scheme != "https" or final.hostname not in {
            "api.github.com", "objects.githubusercontent.com",
            "release-assets.githubusercontent.com",
            "github-releases.githubusercontent.com",
        }:
            raise DownloadError(f"asset download redirected to forbidden host: {final.hostname}")
        with new_regular_output(destination) as output:
            while chunk := response.read(1024 * 1024):
                observed += len(chunk)
                if observed > MAX_ASSET_BYTES:
                    raise DownloadError(f"release asset exceeds size limit: {destination.name}")
                output.write(chunk)
                digest.update(chunk)
    return observed, digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--token-environment", required=True)
    parser.add_argument("--binding", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--inventory", required=True)
    args = parser.parse_args()
    try:
        if args.tag != RELEASE or re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", args.repository) is None:
            raise DownloadError("release tag or repository is not canonical")
        token = os.environ.get(args.token_environment, "")
        if not token:
            raise DownloadError(f"missing token environment variable: {args.token_environment}")
        binding_path = Path(args.binding)
        if not stat.S_ISREG(binding_path.lstat().st_mode) or binding_path.is_symlink():
            raise DownloadError("release binding is not a regular non-symlink")
        binding = json.loads(binding_path.read_text(encoding="utf-8"))
        source = binding.get("paper_c_commit")
        if HEX40.fullmatch(str(source)) is None or binding.get("release") != RELEASE:
            raise DownloadError("release binding has an invalid release/source identity")
        archive = f"paper-c-hardened-public-{source}.tar.zst"
        expected = {archive, f"{archive}.sha256", f"{archive}.verified.json"}
        metadata_url = (
            f"https://api.github.com/repos/{args.repository}/releases/tags/"
            f"{urllib.parse.quote(args.tag, safe='')}"
        )
        release = load_json(metadata_url, token)
        if release.get("tag_name") != args.tag or release.get("draft") is not False:
            raise DownloadError("GitHub release is missing, draft, or has a different tag")
        assets = release.get("assets")
        if not isinstance(assets, list):
            raise DownloadError("GitHub release has no asset inventory")
        by_name: dict[str, dict] = {}
        for asset in assets:
            if not isinstance(asset, dict) or not isinstance(asset.get("name"), str):
                raise DownloadError("malformed GitHub release asset record")
            if asset["name"] in by_name:
                raise DownloadError(f"duplicate GitHub release asset name: {asset['name']}")
            by_name[asset["name"]] = asset
        missing = expected - set(by_name)
        if missing:
            raise DownloadError(f"GitHub release omits required assets: {sorted(missing)}")
        output = Path(args.output_dir)
        if output.exists() or output.is_symlink():
            raise DownloadError("asset output directory must be new")
        output.mkdir(parents=True)
        records = []
        for name in sorted(expected, key=lambda value: value.encode()):
            asset = by_name[name]
            asset_url = asset.get("url")
            if not isinstance(asset_url, str):
                raise DownloadError(f"asset API URL is missing: {name}")
            size, digest = download(asset_url, token, output / name)
            if asset.get("size") != size:
                raise DownloadError(f"downloaded size disagrees with GitHub metadata: {name}")
            records.append({"name": name, "github_asset_id": asset.get("id"), "bytes": size, "sha256": digest})
        inventory_path = Path(args.inventory)
        if inventory_path.exists() or inventory_path.is_symlink():
            raise DownloadError("download inventory path must be new")
        inventory_path.parent.mkdir(parents=True, exist_ok=True)
        inventory_path.write_text(json.dumps({
            "schema": 1,
            "status": "github_release_assets_downloaded",
            "repository": args.repository,
            "release_tag": args.tag,
            "github_release_id": release.get("id"),
            "assets": records,
        }, indent=2) + "\n", encoding="utf-8")
    except (DownloadError, OSError, UnicodeDecodeError, json.JSONDecodeError, urllib.error.URLError) as exc:
        print(f"GITHUB_RELEASE_ASSET_DOWNLOAD: FAIL: {exc}", file=sys.stderr)
        return 1
    print("GITHUB_RELEASE_ASSET_DOWNLOAD: PASS")
    for record in records:
        print(f"{record['sha256']}  {record['name']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
