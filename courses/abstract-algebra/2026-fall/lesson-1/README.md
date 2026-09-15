# First abstract algebra lesson

The student lesson at `index.html` is public and opens directly, without a password or account. `?section=1.1` opens “等价关系与集合的分类”; `?section=1.2` opens “群的概念”. Each has its own navigation and quiz, ordered by the third-edition textbook. The old `#order` anchor opens the powers topic in §1.2; element order is reserved for §1.5.

`math.js` contains the mathematical model; `lesson.js` renders the interactive topics. `reading.css` sets the reading scale, `textbook.css` styles subsection navigation, and `presentation.css` lets desktop teaching use the available window width. Mobile widths below 768 pixels, and coarse-pointer viewports up to 1024 pixels, hide and disable teaching/fullscreen functionality. Desktop teaching still works when the native Fullscreen API is unavailable or rejects a request.

The separate `teaching-plan/` retains its own encrypted content and password entry. Do not replace or expose that material when maintaining the student lesson.

Release: `20260915-textbook-v1`. The lesson adopts the existing sand appearance once for this release; subsequent explicit appearance choices continue to be shared with the course page. Student-facing prose contains course concepts, interaction instructions, exercise guidance and textbook references; implementation notes and design credits belong outside the lesson.

The former student `access.js` and `lesson.enc.json` are retired. There must be no password form, decryption script, login redirect or account dependency in the student lesson's entry point.
