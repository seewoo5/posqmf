-- The site does not contain the files of the repository that the README links to, so relative
-- links are sent to GitHub instead.
local repository = 'https://github.com/seewoo5/posqmf/blob/main/'

function Link(link)
  if not link.target:match('^%a[%w+.-]*:') and not link.target:match('^#') then
    link.target = repository .. link.target
    return link
  end
end
