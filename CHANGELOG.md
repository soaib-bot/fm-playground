# Change Log

## v2.8.0 [2025-11-04]

- ✨ Added SMT Redundancy Checking
- ✨ Added SMT Redundancy Explanation
- ✨ Added Model Iteration for SMT (based on last solver state)
- ✨ Added a new table to the database for storing analysis metadata
- ⚡️ Fixed pinned history not showing and scrolling correctly

## v2.7.9 [2025-10-29]

- ✨ Added SMT Redundancy Checking
- ✨ Rewritten history drawer with additional features (title, tags, pinning)
- ✨ Added new table to the database for storing history metadata
- ⚡️ Added api for history
- ⚡️ Updated api to update metadata
- 📌 Upgrade z3 wasm to 4.15.1

## v2.7.9 [2025-10-24]

- ✨ Added filtering for SMT Diff
- 🥅 Updated error handling for Diff APIs

## v2.7.8 [2025-10-22]

- 🐛 Fixed logic to invoke filters
- 🐛 Fixed diff view not loading correctly from permalink
- 🐛 Fixed dropdown colour on dark mode
- ⚡️ Storing previous and current spec in cache
- 💄 Prettify smt diff witness
- 💄 Disabled sem analysis button on unsupported tools
- 💄 Moved witness to run api rather than separate ones

## v2.7.6 [2025-10-21]

- 🐛 Fixed limboole diff formula error (formula sanitize)
- 💄 Highlighting the compare spec feature

## v2.7.4 [2025-10-20]

- ✨ Added caching and witness iteration for limboole diff
- ✨ Added evaluator for limboole diff
- 🐛 Reset output on new semantic analysis execution
- 💄 Fixed some UI styling issues

## v2.7.3 [2025-10-19]

- 🐛 Fixed auto refresh not working on tool execution

## v2.7.2 [2025-10-18]

- ✨ Added sem relation for smt diff
- ✨ Added permalink feature for diff view
- 🐛 Fixed sem diff not working from permalink
- 🐛 Fixed toggling full screen makes the background dark

## v2.7.0-2.7.1 [2025-10-18]

- ✨ Added Syntactic and Semantic Diff for limboole and smt
- ✨ Added History based on session without login
- ✨ Added documentation for playground usage and development setup (in progress)

## v2.6.14 [2025-08-06]

- ⚡️ Updated smt grammar
- ♻️ Updated LSP wrapper configuration modularity

## v2.6.13 [2025-07-31]

- ✨ Added Navigating back on Alloy Instances #23
- 🐛 Fixed #22 - Not all available command options are displayed.

## v2.6.10-12 [2025-07-01]

- ♻️ Migrate repository from se-buw to fm4se
- ♻️ Moved alloy CSS to alloy tool dir
- 🔧 updated Vite config for local dev

## v2.6.8-9 [2025-06-04]

- 🐛 Fixed Alloy, tabular instance view not showing #17
- 🐛 Fixed Spectra Syntax Highlighting is not working while LSP is enabled #19
- 🐛 Fixed Line Highlighting is not working in the lsp editor #20

## v2.6.7 [2025-06-02]

- 🐛 Fixed language support is not working from permalink

## v2.6.4-6 [2025-06-01]

- ⬆️ Updated python dependencies
- ⬆️ Upgrade flask cors from 5.0.1 to 6.0.0
- ✨ Added script to automatically update the versions
- 🐛 Fixed poetry install in docker with --no-root

## v2.6.1-3 [2025-05-10]

- 🐛 Fixed Maximum call stack size exceeded in validation
- ✨ Added scope provider for spectra workspace
- 🗃️ Storing lsp metadata of spectra in the database.

## v2.6.0 [2025-05-05]

- ✨ Added Spectra language server support

## v2.5.4 [2025-04-27]

- 📌 Bump Python dependencies
- 📌 Bump npm dependencies

## v2.5.3 [2025-04-01]

- 🔧 Added allowed hosts in the vite config file

## v2.5.2 [2025-04-01]

- 📌 Migrated to vite 6
- 📌 Updated python dependencies

## v2.5.1 [2025-03-31]

- ✨ Added materials for spectra
- ✨ Added current variant of (spectra) pattern names, keeping old for backwards compatibility

## v2.5.0 [2025-02-25]

**Added**

- ✨ Updated smt language support with cross-ref and code completion

## v2.4.0 [2024-12-16]

**Changed**

- ✨ Alloy- added support for atoms and skolems when parsing expressions
- 🐛 Alloy- fixed tabular output
- 🐛 Alloy- fixed alloy instance is not updating immediately
- 🐛 Alloy- fixed evaluator cleared up when switching tabs

## v2.3.0 [2024-12-04]

**Changed**

- ✨ Added alloy evaluator
- 🎨 Improved the visualization of alloy text and tabular format
- ⚡️ Switched deprecated method in Java

## v2.2.2 [2024-12-03]

**Changed**

- 📌Bump python dependencies

## v2.2.1 [2024-11-26]

**Changed**

⚡️Set alloy memory usage limit; restart if exceeded
⚡️Using minisat for alloy
🐛Handle label on alloy commands

## v2.2.0 [2024-11-20]

**Added**

- ✨ Added typo validation in Limboole.
- ✨ Storing language support check as metadata

**Changed**

- 🐛 Fixed issue with ascii char recognition
- 🐛 Fixed limboole syntax highlighting
- ♻️ Refactored error messages

## v2.1.1 [2024-11-05]

**Changed**

- 🐛 Fixed Alloy default run command ignoring all facts
- 🧪 Fixed Alloy-api bkoken test cases
- ⚡️ Removed some unused code
- ⚡️ Fixed some code smells

## v2.1.0 [2024-11-01]

**Added**

- ✨ SMT in editor language support (browser worker)
- ✨ Feedback form

## v2.0.0 [2024-10-20]

**Added**

- ⚡️ Added caching mechanism for z3, nuXmv, and Spectra with Redis
- ✨ New api for getting metadata

**Changed**

- 💥 Separated nuxmv, alloy, and z3 api
- 💥 Merged VAL and QBF are merged into SAT
- 🔥 Remove tool specific api
- 🔥 Remove check type for permalink lookup
- 🔥 Remove dark mode (temporarily)
- ♻️ Migrated backend to Flask 3 and poetry
- ♻️ Populating tools dropdown from fmp.conf
- ♻️ Fixed wasm fallback api
- 🎨 Added issue link on error modals
- 🐛Fixed-creating new spec not reseting the editor

## v1.5.0 [2024-10-07]

**Added**

- ✨ Limboole in editor language support (browser worker)
- ✨ Store playground version for future reference

**Changed**

- ⚡Migrated from JavaScript to TypeScript
- ♻️Merged some duplicate API endpoints

## v1.4.2 [2024-09-28]

**What's changed?**

- 📌Bump esbuild from 0.20.2 to 0.21.5
- 📌Bump micromatch from 4.0.5 to 4.0.8
- 📝Added new examples for SAT, SMT, and Alloy
- 📝Linked YouTube playlist on the readme

## v1.4.1 [2024-08-17]

**What's changed?**

- 🐛Fixed #9 - Alloy's subset singnature indication missing in instances
- 🐛Fixed #8 - unexpected behavior on last instance of temporal Alloy models
- 📌Bump axios from 1.6.2 to 1.7.4

## v1.4.0 [2024-08-10]

**What's changed?**

- Added alloy tabular and text output
- Bug Fixed- can't parse alloy integer label
- Fixed- Unicode handling
- Fixed- Alloy timeout
- Disabled next instance button while calculating
- Added rate limiter for alloy
- Added download ext for spectra
- Add SQLite option for local development

## v1.3.0 [2024-07-09]

**What's changed?**

- Removed legacy alloy4fun
- Added new Alloy API with Spring Boot
- Integrated Alloy UI into the main playground
- Fixed #6 Limboole syntax error reporting blocks running
- Removed DB migration on docker
- Fixed spectra line highlighting error
- nuXmv tutorial URL changed
- Updated workflow for docker build

## v1.2.1 [2024-06-09]

**What's changed?**

- Introduce new tool - Spectra Synthesizer
- Line highlighting on the editor on error/core
- Introduced dark mode
- Compressing large response body
- Migrated Z3 to the browser

## v1.1.2 [2024-01-10]

**Fix**

- Syntax highlighting fails when loading from permalinks 9991aa1c9c83c78fbd1d9849b5b80fd8efd19d19
- Handle non-ASCII characters on specification
- nuXmv time-out blocked by Gunicorn
- Store the specification configuration on refresh/redirect
- Exit fullscreen mode with ESC key keeps current ref
- File upload type
- Run button disable failed when running

## v1.1.1 [2024-01-05]

**Fix**

- GitHub link breaks on mobile device
- After loading a spec from the history the output panel keeps the content of previous analyses, and the permalink is not updated
- Keep the selected history highlighted
- The search results reset to all specs after loading a spec

## v1.1.0 [2023-12-28]

**What's changed?**

- Save user theme preference
- Adjust the height on the fullscreen
- Codebase minification on deployment
- Upgrade Alloy-API to the latest maven and java
- Introduce request limit with flask-limiter

**Fix**

- Limboole parsing error #4
- Copying empty permalink
- API response error
- nuXmv copyright notice

## v1.0.0 [2023-12-21]

**What's changed?**

- Completely rewritten frontend with React
- Added login functionality with Google and GitHub
- Added ability to save specifications
- Added ability to download history as JSON
- Search saved history

## v0.1 [2023-12-14]
