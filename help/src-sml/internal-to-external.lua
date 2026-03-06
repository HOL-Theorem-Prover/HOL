
function Link(el)
  if el.target:match("^#") then
    -- Extract the anchor name
    local anchor = el.target:sub(2)
    -- Replace with external link (e.g., to a GitHub page or your site)
    el.target = anchor .. ".html"
  end
  return el
end
