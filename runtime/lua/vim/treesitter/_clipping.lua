-- If you are given a range like { 0, 0, 0, 4 }, you can pass this around to any
-- child LanguageTrees easily. But if you have used a region like the one
-- marked with xs below...
-- 
-- /// xxxxxxxx
-- /// xxxx
-- /// xxxxxxxxxxx
--
-- ... then when your child LanguageTree returns its injection query matches,
-- if those matches are multi-line matches (like a fenced code block in markdown),
-- then they will clobber the starts of lines. You'll get a region like so:
-- 
-- /// xxxxxxxx
-- xxxxxxxx
-- xxxxxxxxxxxxxxx
--
-- And hence any 3rd-level child parsers of that one will be working in a range
-- with some extra comment marks or whatever it is in the middle of it.
--
-- So we have to be careful to split up any ranges when passing them to a child
-- LanguageTree. This file implements that.

local M = {}

-- http://lua-users.org/wiki/BinarySearch
-- Avoid heap allocs for performance
local default_fcompval = function(value)
  return value
end
local fcompf = function(a, b)
  return a < b
end
local fcompr = function(a, b)
  return a > b
end

--- Finds values in a _sorted_ list using binary search.
--- If present, returns the range of indices that are == to `value`
--- If absent, returns the insertion point (duplicated), which may go off the end (#t + 1)
---@return integer range start
---@return integer range end
---@return boolean true if value was present
function M.binsearch(t, value, fcompval, reversed, start_point, end_point)
  -- Initialise functions
  fcompval = fcompval or default_fcompval
  local fcomp = reversed and fcompr or fcompf
  --  Initialise numbers
  local iStart, iEnd, iMid = 1, #t, 0
  if start_point ~= nil then iStart = start_point end
  if end_point ~= nil then iEnd = math.min(iEnd, end_point) end
  local iState = 0
  -- Binary Search
  while iStart <= iEnd do
    -- calculate middle
    iMid = math.floor((iStart + iEnd) / 2)
    -- get compare value
    local value2 = fcompval(t[iMid])
    -- get all values that match
    if value == value2 then
      local tfound, num = { iMid, iMid }, iMid - 1
      while num > 0 and value == fcompval(t[num]) do
        tfound[1], num = num, num - 1
      end
      num = iMid + 1
      while num <= #t and value == fcompval(t[num]) do
        tfound[2], num = num, num + 1
      end
      local from, to = unpack(tfound)
      return from, to, true
      -- keep searching
    elseif fcomp(value, value2) then
      iEnd = iMid - 1
      iState = 0
    else
      iStart = iMid + 1
      iState = 1
    end
  end
  -- modified to return the right place for such a value to be inserted, with 'false'
  -- indicating it wasn't in there already
  return iMid + iState, iMid + iState, false
end

---@param range Range6
---@return integer
---@return integer
local function range_bytes(range)
  return range[3], range[6]
end

--- Sort the 
---@param a Range6
---@param b Range6
local function overlap_cmp(a, b)
  local af, at = range_bytes(a)
  local bf, bt = range_bytes(b)
  if af < bf then
    return true
  elseif at < bt then
    return true
  else
    return false
  end
end

---@param dst Range6
---@param src Range6
local function copy_start(dst, src)
  dst[1] = src[1]
  dst[2] = src[2]
  dst[3] = src[3]
end

---@param dst Range6
---@param src Range6
local function copy_end(dst, src)
  dst[4] = src[4]
  dst[5] = src[5]
  dst[6] = src[6]
end

local function range_start(range)
  return range[3]
end
local function range_end(range)
  return range[6]
end

---@param needle Range6
---@param haystack Range6[]
---@return Range6[]
function M.find_overlaps(needle, haystack)
  -- assume region sorted
  local from, to = range_bytes(needle)
  local istart, _, _ = M.binsearch(haystack, from, range_end)
  local _, iend, exists = M.binsearch(haystack, to, range_start, false, istart)
  if not exists then iend = iend - 1 end
  local slice = {}
  for i = istart,iend do table.insert(slice, haystack[i]) end
  return slice
end

-- This is the idea:
-- parent: xxxxxx    xxxx  xxxxx
-- child:    ----------------
-- result:   oooo    iiii  oo

function M.clip_range_with_overlaps(child, overlapping)
  local child_from, child_to = range_bytes(child)
  local results = {}
  local o2 = {}
  for _, r in pairs(overlapping) do
    table.insert(o2, r)
  end
  table.sort(o2, overlap_cmp)
  overlapping = o2

  local last_f, last_t, last_r, coalesced
  if #overlapping == 0 then
    return results
  end

  last_f, last_t = range_bytes(overlapping[1])
  last_r = { unpack(overlapping[1]) }
  coalesced = {}

  if #overlapping > 1 then
    for i = 2, #overlapping do
      local r = overlapping[i]
      local f, t = range_bytes(r)
      if f <= last_f and t >= last_f then
        -- expand the previous range backwards
        copy_start(last_r, r)
        if t > last_t then
          -- we cover the previous range entirely
          copy_end(last_r, r)
        end
      elseif f >= last_f and f <= last_t and t > last_t then
        -- expand the previous range forwards
        copy_end(last_r, r)
      else
        table.insert(coalesced, last_r)
        last_r = { unpack(r) }
      end
    end
  end
  table.insert(coalesced, last_r)

  for _, parent in ipairs(coalesced) do
    -- remove at some point
    parent = { unpack(parent) }
    -- this would be a zero length range
    if parent[3] >= parent[6] then
      goto continue
    end

    -- parent: xxxxxx    xxxxxxxx
    -- child:    ------    ----
    -- result:   oooo      oooo
    if parent[3] < child_from then
      copy_start(parent, child)
    end

    -- parent:   xxxxxx  xxxxxxxx
    -- child:  ------      ----
    -- result:   oooo      oooo
    if parent[6] > child_to then
      copy_end(parent, child)
    end
    -- this would be a zero length range
    if parent[3] >= parent[6] then
      goto continue
    end
    -- if not modified by previous rules, then it's just wholly contained
    -- parent:   xxxxxx
    -- child:  -----------
    -- result:   iiiiii
    table.insert(results, parent)
    ::continue::
  end

  return results
end

---@param child_region Range6[]
---@param parent_region Range6[]
function M.clip_region(child_region, parent_region)
  if child_region == nil then return {} end
  if not parent_region or #parent_region == 0 then return child_region end
  -- error(vim.inspect({ child_region = child_region, parent_region = parent_region }))
  local clipped_region = {}
  for _, child_range in ipairs(child_region) do
    local overlapping = M.find_overlaps(child_range, parent_region)
    -- error(vim.inspect({ child_range = child_range, overlapping = overlapping, parent_region = parent_region }))
    local clipped = M.clip_range_with_overlaps(child_range, overlapping)
    for _, subrange in ipairs(clipped) do
      table.insert(clipped_region, subrange)
    end
  end
  -- error(vim.inspect({ original = child_region, clipped = clipped_region }))
  return clipped_region
end

return M
