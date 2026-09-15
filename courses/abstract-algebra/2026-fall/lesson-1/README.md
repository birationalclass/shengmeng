# First abstract algebra lesson

The student lesson at `index.html` is public and opens directly, without a password or account. `?section=1.1` opens “等价关系与集合的分类”; `?section=1.2` opens “群的概念”. Each has its own navigation and quiz, ordered by the third-edition textbook. The old `#order` anchor opens the powers topic in §1.2; element order is reserved for §1.5.

`math.js` contains the mathematical model; `lesson.js` renders the interactive topics. `reading.css` sets the reading scale, `textbook.css` styles subsection navigation, and `presentation.css` lets desktop teaching use the available window width. Mobile widths below 768 pixels, and coarse-pointer viewports up to 1024 pixels, hide and disable teaching/fullscreen functionality. Desktop teaching still works when the native Fullscreen API is unavailable or rejects a request.

The separate `teaching-plan/` retains its own encrypted content and password entry. Do not replace or expose that material when maintaining the student lesson.

Release: `20260915-course-screen-v1`. The semester URL hosts the original scrolling course schedule and a viewport-sized lesson. The top contents, previous/next subsection and course buttons change views without reloading the outer page. Existing lesson URLs redirect to this shell; `embedded=1` is the iframe entry. Native fullscreen remains optional and is unavailable on phones.

`screen.css` and `screen.js` paginate overflowing lesson content into accessible columns with visible previous/next controls. Mobile learners switch between concepts and experiments. `exercises.js` contains bilingual, textbook-derived variations with preserved answer and proof progress. `course-language.js`, `course-english.js` and `lesson-english.js` provide local Chinese/English translations. The course schedule retains its original table, filters, search and scrolling layout. Settings use natural dialog height and fixed circular close controls. The opening loader offers an immediate skip even before its controller loads.

The top navigation names adjacent textbook sections. `course-sections.js` lists all 25 sections in Chapters 1–4; sections other than 1.1 and 1.2 currently display explicit blank test pages. The redundant in-lesson section cards are removed. Every property and group criterion starts with a complete statement before an explicit “Begin proof” action; both directions of the equivalence criteria are included.

The lesson adopts the existing sand appearance once; subsequent explicit appearance choices remain shared with the course page. Student-facing prose contains course concepts, interaction instructions, exercise guidance and textbook references; implementation notes belong outside the lesson.

The former student `access.js` and `lesson.enc.json` are retired. There must be no password form, decryption script, login redirect or account dependency in the student lesson's entry point.
