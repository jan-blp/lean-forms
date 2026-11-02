# Complete forms and forms-web, directly or through Lake.
function __forms_lake_start
    set -l words (commandline -opc)
    test (count $words) -ge 3; or return 1
    string match -rq '(^|/)lake$' -- $words[1]; or return 1
    set -l start 2
    while contains -- "$words[$start]" -q --quiet
        set start (math $start + 1)
    end
    test "$words[$start]" = exe; or return 1
    set -l next (math $start + 1)
    contains -- "$words[$next]" forms forms-web; or return 1
    echo (math $start + 2)
end

function __forms_candidates
    set -l words (commandline -opc)
    set -l current (commandline -ct)
    set -l start 2
    if string match -rq '(^|/)lake$' -- $words[1]
        set start (__forms_lake_start); or return
        set -l executable_index (math $start - 1)
        command $words[1] -q exe $words[$executable_index] --complete $words[$start..-1] "$current" 2>/dev/null
    else
        command $words[1] --complete $words[$start..-1] "$current" 2>/dev/null
    end
end

complete -c forms -f -a '(__forms_candidates)'
complete -c forms-web -f -a '(__forms_candidates)'
complete -c lake -n '__forms_lake_start >/dev/null' -f -a '(__forms_candidates)'
