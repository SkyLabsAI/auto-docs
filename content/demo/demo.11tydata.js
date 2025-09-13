export default {
  layout: "page.njk",
  eleventyNavigation: {
    order: 10,
    parent: "demo"
  },
  eleventyComputed: {
    title : (data) =>
      data.title ? data.title : data.page.inputPath.slice(data.page.inputPath.lastIndexOf('/')+1)
  }
};
